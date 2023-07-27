#pragma once
#include "graph/graph.hpp"
#include "graph/graph_utility.hpp"

//
// incidence(g,u)     -> edge_descriptor<VId,false,E,EV> -> {target_id, edge&}
// incidence(g,u,evf) -> edge_descriptor<VId,false,E,EV> -> {target_id, edge&, value}
//
// given:    auto evf = [&g](edge_reference_t<G> uv) { return edge_value(g,uv) };
//
// examples: for([vid, uv]        : incidence(g,uid))
//           for([vid, uv, value] : incidence(g,uid,evf))
//
// Since u is passed to incidence(), there's no need to include Sourced versions of
// incidence().
//
namespace std::graph {


template <adjacency_list G, bool Sourced = false, class EVF = void>
class incidence_iterator;

/**
 * @brief Iterator for an incidence range of edges for a vertex.
 *
 * @tparam G    Graph type
 * @tparam EVF  Edge Value Function type
*/
template <adjacency_list G, bool Sourced, class EVF>
class incidence_iterator : source_vertex<G, ((Sourced && !sourced_adjacency_list<G>) || unordered_edge<G, edge_t<G>>)> {
public:
  using base_type = source_vertex<G, ((Sourced && !sourced_adjacency_list<G>) || unordered_edge<G, edge_t<G>>)>;

  using graph_type      = G;
  using vertex_type     = vertex_t<graph_type>;
  using vertex_id_type  = vertex_id_t<graph_type>;
  using vertex_iterator = vertex_iterator_t<graph_type>;

  using edge_range          = vertex_edge_range_t<graph_type>;
  using edge_iterator       = vertex_edge_iterator_t<graph_type>;
  using edge_type           = edge_t<graph_type>;
  using edge_reference_type = edge_reference_t<graph_type>;
  using edge_value_type     = invoke_result_t<EVF, edge_reference_type>;

  using iterator_category = forward_iterator_tag;
  using value_type        = edge_descriptor<const vertex_id_type, Sourced, edge_reference_type, edge_value_type>;
  using difference_type   = ranges::range_difference_t<edge_range>;
  using pointer           = value_type*;
  using const_pointer     = const value_type*;
  using reference         = value_type&;
  using const_reference   = const value_type&;
  using rvalue_reference  = value_type&&;

public:
  incidence_iterator(graph_type& g, vertex_iterator ui, edge_iterator iter, const EVF& value_fn)
        : base_type(vertex_id(g, ui)), g_(g), iter_(iter), value_fn_(&value_fn) {}
  incidence_iterator(graph_type& g, vertex_id_type uid, const EVF& value_fn)
        : base_type(uid), g_(g), iter_(ranges::begin(edges(g, uid))), value_fn_(&value_fn) {}

  constexpr incidence_iterator()                          = default;
  constexpr incidence_iterator(const incidence_iterator&) = default;
  constexpr incidence_iterator(incidence_iterator&&)      = default;
  constexpr ~incidence_iterator()                         = default;

  constexpr incidence_iterator& operator=(const incidence_iterator&) = default;
  constexpr incidence_iterator& operator=(incidence_iterator&&)      = default;

protected:
  // avoid difficulty in undefined vertex reference value in value_type
  // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
  using shadow_edge_type = remove_reference_t<edge_reference_type>;
  using shadow_value_type =
        edge_descriptor<vertex_id_type, Sourced, shadow_edge_type*, _detail::ref_to_ptr<edge_value_type>>;

public:
  constexpr reference operator*() const {
    if constexpr (unordered_edge<G, edge_type>) {
      if (target_id(g_, *iter_) != this->source_vertex_id()) {
        value_.source_id = source_id(g_, *iter_);
        value_.target_id = target_id(g_, *iter_);
      } else {
        value_.source_id = target_id(g_, *iter_);
        value_.target_id = source_id(g_, *iter_);
      }
    } else if constexpr (Sourced) {
      if constexpr (sourced_adjacency_list<G>) {
        value_.source_id = source_id(g_, *iter_);
        value_.target_id = target_id(g_, *iter_);
      } else {
        value_.source_id = this->source_vertex_id();
        value_.target_id = target_id(g_, *iter_);
      }
    } else {
      value_.target_id = target_id(g_, *iter_);
    }
    value_.edge  = &*iter_;
    value_.value = invoke(*value_fn_, *iter_);
    return reinterpret_cast<reference>(value_);
  }

  constexpr incidence_iterator& operator++() {
    ++iter_;
    return *this;
  }
  constexpr incidence_iterator operator++(int) const {
    incidence_iterator tmp(*this);
    ++*this;
    return tmp;
  }

  constexpr bool operator==(const incidence_iterator& rhs) const { return iter_ == rhs.iter_; }
  //constexpr bool operator==(const incidence_iterator& rhs) const { return iter_ == rhs; }

private: // member variables
  mutable shadow_value_type        value_ = {};
  _detail::ref_to_ptr<graph_type&> g_;
  edge_iterator                    iter_;
  const EVF*                       value_fn_ = nullptr;

  friend bool operator==(const edge_iterator& lhs, const incidence_iterator& rhs) { return lhs == rhs.iter_; }
};


template <adjacency_list G, bool Sourced>
class incidence_iterator<G, Sourced, void>
      : public source_vertex<G, ((Sourced && !sourced_adjacency_list<G>) || unordered_edge<G, edge_t<G>>)> {
public:
  using base_type = source_vertex<G, ((Sourced && !sourced_adjacency_list<G>) || unordered_edge<G, edge_t<G>>)>;

  using graph_type      = G;
  using vertex_type     = vertex_t<graph_type>;
  using vertex_id_type  = vertex_id_t<graph_type>;
  using vertex_iterator = vertex_iterator_t<graph_type>;

  using edge_range          = vertex_edge_range_t<graph_type>;
  using edge_iterator       = vertex_edge_iterator_t<graph_type>;
  using edge_type           = edge_t<graph_type>;
  using edge_reference_type = edge_reference_t<graph_type>;
  using edge_value_type     = void;

  using iterator_category = forward_iterator_tag;
  using value_type        = edge_descriptor<const vertex_id_type, Sourced, edge_reference_type, edge_value_type>;
  using difference_type   = ranges::range_difference_t<edge_range>;
  using pointer           = value_type*;
  using const_pointer     = const value_type*;
  using reference         = value_type&;
  using const_reference   = const value_type&;
  using rvalue_reference  = value_type&&;

protected:
  // avoid difficulty in undefined vertex reference value in value_type
  // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
  using shadow_edge_type  = remove_reference_t<edge_reference_type>;
  using shadow_value_type = edge_descriptor<vertex_id_type, Sourced, shadow_edge_type*, edge_value_type>;

public:
  incidence_iterator(graph_type& g, vertex_iterator ui, edge_iterator iter)
        : base_type(vertex_id(g, ui)), g_(g), iter_(iter) {}
  incidence_iterator(graph_type& g, vertex_id_type uid) : base_type(uid), g_(g), iter_(ranges::begin(edges(g, uid))) {}

  constexpr incidence_iterator()                          = default;
  constexpr incidence_iterator(const incidence_iterator&) = default;
  constexpr incidence_iterator(incidence_iterator&&)      = default;
  constexpr ~incidence_iterator()                         = default;

  constexpr incidence_iterator& operator=(const incidence_iterator&) = default;
  constexpr incidence_iterator& operator=(incidence_iterator&&)      = default;

public:
  constexpr reference operator*() const {
    if constexpr (unordered_edge<G, edge_type>) {
      static_assert(sourced_adjacency_list<G>);
      if (target_id(g_, *iter_) != this->source_vertex_id()) {
        value_.source_id = source_id(g_.*iter_);
        value_.target_id = target_id(g_, *iter_);
      } else {
        value_.source_id = target_id(g_.*iter_);
        value_.target_id = source_id(g_, *iter_);
      }
    } else if constexpr (Sourced) {
      if constexpr (sourced_adjacency_list<G>) {
        value_.source_id = source_id(g_, *iter_);
        value_.target_id = target_id(g_, *iter_);
      } else {
        value_.source_id = this->source_vertex_id();
        value_.target_id = target_id(g_, *iter_);
      }
    } else {
      value_.target_id = target_id(g_, *iter_);
    }
    value_.edge = &*iter_;
    return reinterpret_cast<reference>(value_);
  }

  constexpr incidence_iterator& operator++() {
    ++iter_;
    return *this;
  }
  constexpr incidence_iterator operator++(int) const {
    incidence_iterator tmp(*this);
    ++*this;
    return tmp;
  }

  constexpr bool operator==(const incidence_iterator& rhs) const { return iter_ == rhs.iter_; }
  //constexpr bool operator==(const incidence_iterator& rhs) const { return iter_ == rhs; }

private: // member variables
  mutable shadow_value_type        value_ = {};
  _detail::ref_to_ptr<graph_type&> g_;
  edge_iterator                    iter_;

  friend bool operator==(const edge_iterator& lhs, const incidence_iterator& rhs) { return lhs == rhs.iter_; }
};

template <class G, bool Sourced, class EVF>
using incidence_view = ranges::subrange<incidence_iterator<G, Sourced, EVF>, vertex_edge_iterator_t<G>>;
} // namespace std::graph


#ifdef NEW_CPO
namespace std::graph::views {

namespace _Incidence {
  template <class _G>
  concept _Has_all = _Has_class_or_enum_type<_G> //
                     && requires(_G&& __g, vertex_id_t<_G> uid) {
                          { _Fake_copy_init(incidence(__g, uid)) } -> ranges::forward_range;
                        };

  template <class _G, class EVF>
  concept _Has_all_vvf = _Has_class_or_enum_type<_G>             //
                         && invocable<EVF, edge_reference_t<_G>> //
                         && requires(_G&& __g, vertex_id_t<_G>& uid, const EVF& evf) {
                              { _Fake_copy_init(incidence(__g, uid, evf)) } -> ranges::forward_range;
                            };

  class _Cpo {
  private:
    template <class _G>
    struct _value_fnc {
      _value_fnc() = default;
      // return of int is a placeholder; actual EVF may return a diff type
      constexpr int operator()(edge_reference_t<_G>) const noexcept;
    };

    enum class _St_all_opt { _None, _Non_member };
    enum class _St_all_evf_opt { _None, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_all_opt> _Choose_all_opt() noexcept {
      if constexpr (_Has_all<_G>) {
        return {_St_all_opt::_Non_member,
                noexcept(_Fake_copy_init(incidence(declval<_G>(), declval<vertex_id_t<_G>>())))};
      } else {
        return {_St_all_opt::_None};
      }
    }
    template <class _G>
    static constexpr _Choice_t<_St_all_opt> _Choice_all = _Choose_all_opt<_G>();

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_all_evf_opt> _Choose_all_evf_opt() noexcept {
      if constexpr (_Has_all_vvf<_G>) {
        return {_St_all_evf_opt::_Non_member,
                noexcept(_Fake_copy_init(
                      incidence(std::declval<_G>(), declval<vertex_id_t<_G>>(), std::declval<_value_fnc>())))};
      } else {
        return {_St_all_evf_opt::_None};
      }
    }
    template <class _G>
    static constexpr _Choice_t<_St_all_evf_opt> _Choice_all_evf = _Choose_all_evf_opt<_G>();

  public:
    /**
     * @brief Get incidence edges of a vertex in a graph.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: incidence_view<_G, false, void>(incidence_iterator<_G, false, void>(__g, uid),
                                               ranges::end(edges(__g, uid)))
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uid Vertex id to get the outgoing edges for.
     * @return The range of outgoing edges on a vertex with value_type of edge_descriptor<vertex_id_t<G>, false, edge_reference_t<G>>.
    */
    template <class _G>
    [[nodiscard]] constexpr auto operator()(_G&& __g, vertex_id_t<_G>& uid) const noexcept(_Choice_all<_G>._No_throw) {
      if constexpr (_Choice_all<_G>()._Strategy == _St_all_opt::_Non_member) {
        return incidence(std::forward<_G>(__g, uid));
      } else {
        return incidence_view<_G, false, void>(incidence_iterator<_G, false, void>(__g, uid),
                                               ranges::end(edges(__g, uid)));
      }
    }

    /**
     * @brief Get incidence edges of a vertex in a graph with projected values.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: incidence_view<_G, false, EVF>(incidence_iterator<_G, false, EVF>(__g, uid, value_fn),
     *                                                        ranges::end(edges(__g, uid)));
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uid Vertex id to get the outgoing edges for
     * @param value_fn(edge_reference_t<G>) that returns a edge value.
     * @return The range of all outgoing edges of a vertex with value_type of edge_descriptor<vertex_id_t<G>, false, edge_reference<G>, decltype(value_fn())>.
    */
    template <class _G, class EVF>
    requires invocable<EVF, edge_reference_t<_G>>
    [[nodiscard]] constexpr auto operator()(_G&& __g, vertex_id_t<_G> uid, EVF&& value_fn) const
          noexcept(_Choice_all_evf<_G>._No_throw) {
      if constexpr (_Choice_all_evf<_G>()._Strategy == _St_all_opt::_Non_member) {
        return incidence(std::forward<_G>(__g), uid, value_fn);
      } else {
        return incidence_view<_G, false, EVF>(incidence_iterator<_G, false, EVF>(__g, uid, value_fn),
                                              ranges::end(edges(__g, uid)));
      }
    }
  };

} // namespace _Incidence


inline namespace _Cpos {
  inline constexpr _Incidence::_Cpo incidence;
}
} // namespace std::graph::views

#else
namespace std::graph::tag_invoke {
// ranges
TAG_INVOKE_DEF(incidence); // incidence(g,uid)            -> edges[vid,v]
                           // incidence(g,uid,fn)         -> edges[vid,v,value]

template <class G>
concept _has_incidence_g_uid_adl = vertex_range<G> && requires(G&& g, vertex_id_t<G> uid) {
  { incidence(g, uid) };
};
template <class G, class EVF>
concept _has_incidence_g_uid_evf_adl = vertex_range<G> && requires(G&& g, vertex_id_t<G> uid, const EVF& evf) {
  { incidence(g, uid, evf) };
};
} // namespace std::graph::tag_invoke

namespace std::graph::views {
//
// incidence(g,uid)
//
template <adjacency_list G>
requires ranges::forward_range<vertex_range_t<G>>
constexpr auto incidence(G&& g, vertex_id_t<G> uid) {
  if constexpr (std::graph::tag_invoke::_has_incidence_g_uid_adl<G>)
    return std::graph::tag_invoke::incidence(g, uid);
  else
    return incidence_view<G, false, void>(incidence_iterator<G, false, void>(g, uid), ranges::end(edges(g, uid)));
}


//
// incidence(g,uid,evf)
//
template <adjacency_list G, class EVF>
requires ranges::forward_range<vertex_range_t<G>>
constexpr auto incidence(G&& g, vertex_id_t<G> uid, const EVF& evf) {
  if constexpr (std::graph::tag_invoke::_has_incidence_g_uid_evf_adl<G, EVF>)
    return std::graph::tag_invoke::incidence(g, uid, evf);
  else
    return incidence_view<G, false, EVF>(incidence_iterator<G, false, EVF>(g, uid, evf), ranges::end(edges(g, uid)));
}

} // namespace std::graph::views
#endif
