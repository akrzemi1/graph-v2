#pragma once
#include "graph/graph.hpp"
#include "graph/graph_utility.hpp"

//
// vertexlist(g) -> vertex_descriptor<VId,V,VV> -> {id, vertex& [,value]}
//
// given:    vvf = [&g](vertex_reference_t<G> u) -> decl_type(vertex_value(g)) { return vertex_value(g,u);}
//           (trailing return type is required if defined inline as vertexlist parameter)
//
//           vertex_iterator<G> first = ..., last = ...;
//
// examples: for(auto&& [uid, u]      : vertexlist(g))
//         : for(auto&& [uid, u, val] : vertexlist(g,vvf)
//
//         : for(auto&& [uid, u]      : vertexlist(g, first, last))
//         : for(auto&& [uid, u, val] : vertexlist(g, first, last, vvf)
//
//         : for(auto&& [uid, u]      : vertexlist(g, vr))
//         : for(auto&& [uid, u, val] : vertexlist(g, vr, vvf)
//
namespace std::graph {

template <adjacency_list G, class VVF = void>
requires ranges::forward_range<vertex_range_t<G>> && integral<vertex_id_t<G>>
class vertexlist_iterator;


template <adjacency_list G, class VVF>
requires ranges::forward_range<vertex_range_t<G>> && integral<vertex_id_t<G>>
class vertexlist_iterator {
public:
  using graph_type            = G;
  using vertex_id_type        = vertex_id_t<graph_type>;
  using vertex_range_type     = vertex_range_t<graph_type>;
  using vertex_iterator_type  = ranges::iterator_t<vertex_range_type>;
  using vertex_type           = vertex_t<graph_type>;
  using vertex_reference_type = ranges::range_reference_t<vertex_range_type>;
  using vertex_value_func     = VVF;
  using vertex_value_type     = invoke_result_t<VVF, vertex_type&>;

  using iterator_category = forward_iterator_tag;
  using value_type        = vertex_descriptor<const vertex_id_t<graph_type>, vertex_reference_type, vertex_value_type>;
  using difference_type   = ranges::range_difference_t<vertex_range_type>;
  using pointer           = value_type*;
  using const_pointer     = const value_type*;
  using reference         = value_type&;
  using const_reference   = const value_type&;

protected:
  // use of shadow_vertex_type avoids difficulty in undefined vertex reference value in value_type
  // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
  using shadow_vertex_type = remove_reference_t<vertex_reference_type>;
  using shadow_value_type =
        vertex_descriptor<vertex_id_t<graph_type>, shadow_vertex_type*, _detail::ref_to_ptr<vertex_value_type>>;

public:
  vertexlist_iterator(graph_type& g, const VVF& value_fn, vertex_iterator_type iter, vertex_id_type start_at = 0)
        : iter_(iter), value_fn_(&value_fn) {
    value_.id = start_at;
  }

  constexpr vertexlist_iterator()                           = default;
  constexpr vertexlist_iterator(const vertexlist_iterator&) = default;
  constexpr vertexlist_iterator(vertexlist_iterator&&)      = default;
  constexpr ~vertexlist_iterator()                          = default;

  constexpr vertexlist_iterator& operator=(const vertexlist_iterator&) = default;
  constexpr vertexlist_iterator& operator=(vertexlist_iterator&&)      = default;

public:
  constexpr reference operator*() const {
    value_.vertex = &*iter_;
    if constexpr (!is_void_v<vertex_value_type>)
      value_.value = invoke(*this->value_fn_, *iter_);
    return reinterpret_cast<reference>(value_);
  }

  constexpr vertexlist_iterator& operator++() {
    ++iter_;
    ++value_.id;
    // leave value_.vertex as-is to avoid dereferencing iter_ when it's at end()
    return *this;
  }
  constexpr vertexlist_iterator operator++(int) const {
    vertexlist_iterator tmp(*this);
    ++*this;
    return tmp;
  }

  constexpr bool operator==(const vertexlist_iterator& rhs) const { return iter_ == rhs.iter_; }

protected:
  mutable shadow_value_type value_ = {};
  vertex_iterator_type      iter_;
  const VVF*                value_fn_ = nullptr;

  friend bool operator==(const vertex_iterator_type& lhs, const vertexlist_iterator& rhs) { return lhs == rhs.iter_; }
};


template <adjacency_list G>
requires ranges::forward_range<vertex_range_t<G>> && integral<vertex_id_t<G>>
class vertexlist_iterator<G, void> {
public:
  using graph_type            = G;
  using vertex_id_type        = vertex_id_t<graph_type>;
  using vertex_range_type     = vertex_range_t<graph_type>;
  using vertex_iterator_type  = ranges::iterator_t<vertex_range_type>;
  using vertex_type           = vertex_t<graph_type>;
  using vertex_reference_type = ranges::range_reference_t<vertex_range_type>;
  using vertex_value_func     = void;
  using vertex_value_type     = void;

  using iterator_category = forward_iterator_tag;
  using value_type        = vertex_descriptor<const vertex_id_type, vertex_reference_type, void>;
  using difference_type   = ranges::range_difference_t<vertex_range_type>;
  using pointer           = value_type*;
  using const_pointer     = const value_type*;
  using reference         = value_type&;
  using const_reference   = const value_type&;
  using rvalue_reference  = value_type&&;

protected:
  // avoid difficulty in undefined vertex reference value in value_type
  // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
  using shadow_vertex_type = remove_reference_t<vertex_reference_type>;
  using shadow_value_type  = vertex_descriptor<vertex_id_type, shadow_vertex_type*, void>;

public:
  vertexlist_iterator(graph_type& g) : iter_(ranges::begin(vertices(const_cast<graph_type&>(g)))) {}
  vertexlist_iterator(vertex_iterator_type iter, vertex_id_type start_at = 0)
        : value_{start_at, nullptr}, iter_(iter) {}

  constexpr vertexlist_iterator()                           = default;
  constexpr vertexlist_iterator(const vertexlist_iterator&) = default;
  constexpr vertexlist_iterator(vertexlist_iterator&&)      = default;
  constexpr ~vertexlist_iterator()                          = default;

  constexpr vertexlist_iterator& operator=(const vertexlist_iterator&) = default;
  constexpr vertexlist_iterator& operator=(vertexlist_iterator&&)      = default;

public:
  constexpr reference operator*() const {
    value_.vertex = &*iter_;
    if constexpr (!is_void_v<vertex_value_type>)
      value_.value = this->value_fn_(*iter_);
    return reinterpret_cast<reference>(value_);
  }

  constexpr vertexlist_iterator& operator++() {
    ++iter_;
    ++value_.id;
    // leave value_.vertex as-is to avoid dereferencing iter_ to get value_.vertex when it's at end()
    return *this;
  }
  constexpr vertexlist_iterator operator++(int) const {
    vertexlist_iterator tmp(*this);
    ++*this;
    return tmp;
  }

  constexpr bool operator==(const vertexlist_iterator& rhs) const { return iter_ == rhs.iter_; }

protected:
  mutable shadow_value_type value_ = {};
  vertex_iterator_type      iter_;

  friend bool operator==(const vertex_iterator_type& lhs, const vertexlist_iterator& rhs) { return lhs == rhs.iter_; }
};


template <adjacency_list G, class VVF = void>
using vertexlist_view = ranges::subrange<vertexlist_iterator<G, VVF>, vertex_iterator_t<G>>;
} // namespace std::graph

#ifdef NEW_CPO
namespace std::graph::views {

// vertexlist(g)               -> vertex_descriptor[uid,u]
// vertexlist(g,fn)            -> vertex_descriptor[uid,u,value]
// vertexlist(g,first,last)    -> vertex_descriptor[uid,u]
// vertexlist(g,first,last,fn) -> vertex_descriptor[uid,u,value]
namespace _Vertexlist {
#  if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void vertexlist() = delete;                // Block unqualified name lookup
#  else                                      // ^^^ no workaround / workaround vvv
  void vertexlist();
#  endif                                     // ^^^ workaround ^^^

  template <class _G>
  concept _Has_all = _Has_class_or_enum_type<_G> //
                     && requires(_G&& __g) {
                          { _Fake_copy_init(vertexlist(__g)) } -> ranges::forward_range;
                        };

  template <class _G, class VVF>
  concept _Has_all_vvf = _Has_class_or_enum_type<_G>               //
                         && invocable<VVF, vertex_reference_t<_G>> //
                         && requires(_G&& __g, const VVF& vvf) {
                              { _Fake_copy_init(vertexlist(__g, vvf)) } -> ranges::forward_range;
                            };

  template <class _G>
  concept _Has_iter_rng = _Has_class_or_enum_type<_G> //
                          && requires(_G&& __g, vertex_iterator_t<_G> ui, vertex_iterator_t<_G> vi) {
                               { _Fake_copy_init(vertexlist(__g, ui, vi)) } -> ranges::forward_range;
                             };

  template <class _G, class VVF>
  concept _Has_iter_rng_vvf =
        _Has_class_or_enum_type<_G> //
        && requires(_G&& __g, vertex_iterator_t<_G> ui, vertex_iterator_t<_G> vi, const VVF& vvf) {
             { _Fake_copy_init(vertexlist(__g, ui, vi, vvf)) } -> ranges::forward_range;
           };


  class _Cpo {
  private:
    enum class _St_opt { _None, _All, _All_vvf, _Rng, _Rng_vvf };

    enum class _St_id { _None, _Non_member, _Auto_eval };
    enum class _St_ref { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_opt> _Choose_opt() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_all<_G>) {
        return {_St_opt::_All, noexcept(_Fake_copy_init(vertexlist(declval<_G>())))};
      } else if constexpr (_Has_all_vvf<_G>) {
        return {_St_opt::_All, noexcept(_Fake_copy_init(vertexlist(declval<_G>(), declval<vertex_iterator_t<_G>>(),
                                                                   declval<vertex_iterator_t<_G>>())))};
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_opt> _Choose_opt() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_all<_G>) {
        return {_St_opt::_All, noexcept(_Fake_copy_init(vertexlist(declval<_G>())))};
      } else if constexpr (_Has_all_vvf<_G>) {
        return {_St_opt::_All, noexcept(_Fake_copy_init(vertexlist(declval<_G>(), declval<vertex_iterator_t<_G>>(),
                                                                   declval<vertex_iterator_t<_G>>())))};
      } else {
        return {_St_ref::_None};
      }
    }


  public:
    /**
     * @brief Get the outgoing vertexlist of a vertex.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: n/a. This must be specialized for each graph type.
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param u Vertex reference.
     * @return A range of the outgoing vertexlist.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, vertex_reference_t<_G> u) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_ref = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_ref == _St_ref::_Member) {
        return __g.vertexlist(u);
      } else if constexpr (_Strat_ref == _St_ref::_Non_member) {
        return vertexlist(__g, u); // intentional ADL
      } else {
        static_assert(_Always_false<_G>, "vertexlist(g,u) is not defined");
      }
    }

    /**
     * @brief Get the outgoing vertexlist of a vertex id.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: vertexlist(g, *find_vertex(g, uid))
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uid Vertex id.
     * @return A range of the outgoing vertexlist.
    */
    template <class _G>
    requires(_Choice_id<_G&>._Strategy != _St_id::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, const vertex_id_t<_G>& uid) const
          noexcept(_Choice_id<_G&>._No_throw) {
      constexpr _St_id _Strat_id = _Choice_id<_G&>._Strategy;

      if constexpr (_Strat_id == _St_id::_Non_member) {
        return vertexlist(__g, uid);                 // intentional ADL
      } else if constexpr (_Strat_id == _St_id::_Auto_eval) {
        return (*this)(__g, *find_vertex(__g, uid)); // default impl
      } else {
        static_assert(_Always_false<_G>,
                      "vertexlist(g,uid) is not defined and default implementation cannot be evaluated");
      }
    }
  };
} // namespace _Vertexlist

inline namespace _Cpos {
  inline constexpr _Vertexlist::_Cpo vertexlist;
}
} // namespace std::graph::views
#else
namespace std::graph::tag_invoke {
// ranges
TAG_INVOKE_DEF(vertexlist); // vertexlist(g)               -> vertices[uid,u]
                            // vertexlist(g,fn)            -> vertices[uid,u,value]
                            // vertexlist(g,first,last)    -> vertices[uid,u]
                            // vertexlist(g,first,last,fn) -> vertices[uid,u,value]

template <class G>
concept _has_vertexlist_g_adl = vertex_range<G> && requires(G&& g) {
  { vertexlist(g) };
};

template <class G, class VVF>
concept _has_vertexlist_g_fn_adl =
      vertex_range<G> && invocable<VVF, vertex_reference_t<G>> && requires(G&& g, const VVF& fn) {
        { vertexlist(g, fn) };
      };

template <class G>
concept _has_vertexlist_i_i_adl = vertex_range<G> && requires(G&& g, vertex_iterator_t<G> ui, vertex_iterator_t<G> vi) {
  { vertexlist(g, ui, vi) };
};

template <class G, class VVF>
concept _has_vertexlist_i_i_fn_adl = vertex_range<G> && invocable<VVF, vertex_reference_t<G>> &&
                                     requires(G&& g, vertex_iterator_t<G> ui, vertex_iterator_t<G> vi, const VVF& fn) {
                                       { vertexlist(g, ui, vi, fn) };
                                     };

template <class G, class VR>
concept _has_vertexlist_vrng_adl =
      vertex_range<G> && ranges::random_access_range<VR> && requires(G&& g, vertex_range_t<G>& vr) {
        { vertexlist(g, vr) };
      };

template <class G, class VR, class VVF>
concept _has_vertexlist_vrng_fn_adl =
      vertex_range<G> && ranges::random_access_range<VR> && convertible_to<ranges::range_value_t<VR>, vertex_t<G>> &&
      invocable<VVF, vertex_reference_t<G>> && requires(G&& g, VR&& vr, const VVF& fn) {
        { vertexlist(g, vr, fn) };
      };


} // namespace std::graph::tag_invoke
#endif

namespace std::graph::views {
//
// vertexlist(g [,proj])
//
template <adjacency_list G>
constexpr auto vertexlist(G&& g) {
  if constexpr (std::graph::tag_invoke::_has_vertexlist_g_adl<G>)
    return std::graph::tag_invoke::vertexlist(forward<G>(g));
  else {
    //auto&& v = vertices(std::forward<G>(g));
    //static_assert(std::ranges::range<decltype(v)>);
    //static_assert(std::is_convertible_v<decltype(v), vertices_t<G>>);
    //return vertexlist_view<G>(v);
    return vertexlist_view<G>(vertices(std::forward<G>(g)));
  }
}

template <adjacency_list G, class VVF>
requires invocable<VVF, vertex_reference_t<G>>
constexpr auto vertexlist(G&& g, const VVF& value_fn) {
  using iterator_type = vertexlist_iterator<G, VVF>;
  if constexpr (std::graph::tag_invoke::_has_vertexlist_g_fn_adl<G, VVF>)
    return std::graph::tag_invoke::vertexlist(forward<G>(g), value_fn);
  else
    return vertexlist_view<G, VVF>(iterator_type(forward<G>(g), value_fn, begin(vertices(forward<G>(g)))),
                                   end(vertices(forward<G>(g))));
}

//
// vertexlist(g, first, last [,proj])
//
template <adjacency_list G>
requires ranges::random_access_range<vertex_range_t<G>>
constexpr auto vertexlist(G&& g, vertex_iterator_t<G> first, vertex_iterator_t<G> last) {
  using iterator_type = vertexlist_iterator<G>;
  if constexpr (std::graph::tag_invoke::_has_vertexlist_i_i_adl<G>)
    return std::graph::tag_invoke::vertexlist(forward<G>(g), first, last);
  else
    return vertexlist_view<G>(iterator_type(first, static_cast<vertex_id_t<G>>(first - begin(vertices(g)))), last);
}

template <adjacency_list G, class VVF>
requires ranges::random_access_range<vertex_range_t<G>> && invocable<VVF, vertex_reference_t<G>>
constexpr auto vertexlist(G&& g, vertex_iterator_t<G> first, vertex_iterator_t<G> last, const VVF& value_fn) {
  using iterator_type = vertexlist_iterator<G, VVF>;
  if constexpr (std::graph::tag_invoke::_has_vertexlist_i_i_fn_adl<G, VVF>)
    return std::graph::tag_invoke::vertexlist(forward<G>(g), first, last, value_fn);
  else {
    auto first_id = static_cast<vertex_id_t<G>>(first - begin(vertices(g)));
    return vertexlist_view<G, VVF>(iterator_type(forward<G>(g), value_fn, first), last, first_id);
  }
}

//
// vertexlist(g, ur, [,proj])
//
template <adjacency_list G, ranges::random_access_range VR>
requires ranges::random_access_range<vertex_range_t<G>>
constexpr auto vertexlist(G&& g, VR&& vr) {
  using iterator_type = vertexlist_iterator<G>;
  if constexpr (std::graph::tag_invoke::_has_vertexlist_vrng_adl<G, VR>)
    return std::graph::tag_invoke::vertexlist(forward<G>(g), forward<VR>(vr));
  else {
    auto first    = ranges::begin(vr);
    auto last     = ranges::end(vr);
    auto first_id = static_cast<vertex_id_t<G>>(first - begin(vertices(g)));
    return vertexlist_view<G>(iterator_type(first, first_id), last);
  }
}

template <adjacency_list G, ranges::random_access_range VR, class VVF>
requires invocable<VVF, vertex_reference_t<G>> &&
         convertible_to<ranges::iterator_t<VR>, vertex_iterator_t<G>> // allow for ranges::subrange of vertices
constexpr auto vertexlist(G&& g, VR&& vr, const VVF& value_fn) {
  using iterator_type = vertexlist_iterator<G, VVF>;
  if constexpr (std::graph::tag_invoke::_has_vertexlist_vrng_fn_adl<G, VR, VVF>)
    return std::graph::tag_invoke::vertexlist(forward(g), forward(vr), value_fn);
  else {
    auto first    = ranges::begin(vr);
    auto last     = ranges::end(vr);
    auto first_id = static_cast<vertex_id_t<G>>(first - begin(vertices(g)));
    return vertexlist_view<G, VVF>(iterator_type(forward<G>(g), value_fn, first, first_id), last);
  }
}


} // namespace std::graph::views
