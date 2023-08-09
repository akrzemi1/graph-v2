#pragma once
#include "graph/graph.hpp"

//
// edgelist(g,u) -> edge_descriptor<VId,true,E,EV> -> {source_id, target_id, edge& [,value]}
//
// given:    auto evf = [&g](edge_reference_t<G> uv) { return edge_value(uv); }
//
//           vertex_id<G> first_id = ..., last_id = ...;
//
// examples: for([uid, vid, uv]        : edgelist(g))
//           for([uid, vid, uv, value] : edgelist(g,evf))
//
//           for([uid, vid, uv]        : edgelist(g,first_id,last_id))
//           for([uid, vid, uv, value] : edgelist(g,first_id,last_id,evf))
//
namespace std::graph::views {


template <adjacency_list G, class EVF = void>
class edgelist_iterator;


template <adjacency_list G>
class edgelist_iterator_base {
  using vertex_iterator = vertex_iterator_t<G>;
  using edge_iterator   = vertex_edge_iterator_t<G>;

protected:
  /**
   * If the current vertex is non-empty then uvi is set to begin(edges(g,*ui)).
   * Otherwise, skip past vertices until we find one with edges, and set uvi to the first edge.
   * If no vertices with edges are found, ui = end(vertices(g)).
   *
   * @param g   Graph instance
   * @param ui  Current vertex
   * @param uvi Current edge
  */
  constexpr void find_non_empty_vertex(G& g, vertex_iterator& ui, edge_iterator& uvi) noexcept {
    for (; ui != ranges::end(vertices(g)); ++ui) {
      if (!ranges::empty(edges(g, *ui))) {
        uvi = ranges::begin(edges(g, *ui));
        return;
      }
    }
  }

  /**
   * @brief Find the next edge. 
   *
   * Assumes current vertex & edge iterators point to valid objects.
   * 
   * @param g   Graph instance
   * @param ui  Current vertex
   * @param uvi Current edge
  */
  constexpr void find_next_edge(G& g, vertex_iterator& ui, edge_iterator& uvi) noexcept {
    assert(ui != ranges::end(vertices(g)));
    assert(uvi != ranges::end(edges(g, *ui)));
    if (++uvi != ranges::end(edges(g, *ui)))
      return;
    ++ui;
    find_non_empty_vertex(g, ui, uvi);
  }
};


/**
 * @brief Iterator for an edgelist range of edges for a vertex.
 *
 * @tparam G    Graph type
 * @tparam EVF  Edge Value Function type
*/
template <adjacency_list G, class EVF>
class edgelist_iterator : public edgelist_iterator_base<G> {
public:
  using base_type = edgelist_iterator_base<G>;

  using graph_type      = G;
  using vertex_type     = vertex_t<graph_type>;
  using vertex_id_type  = vertex_id_t<graph_type>;
  using vertex_iterator = vertex_iterator_t<G>;

  using edge_range          = vertex_edge_range_t<graph_type>;
  using edge_iterator       = vertex_edge_iterator_t<graph_type>;
  using edge_type           = edge_t<graph_type>;
  using edge_reference_type = edge_reference_t<graph_type>;
  using edge_value_type     = invoke_result_t<EVF, edge_reference_type>;

  using iterator_category = forward_iterator_tag;
  using value_type        = edge_descriptor<const vertex_id_type, true, edge_reference_type, edge_value_type>;
  using difference_type   = ranges::range_difference_t<edge_range>;
  using pointer           = value_type*;
  using const_pointer     = const value_type*;
  using reference         = value_type&;
  using const_reference   = const value_type&;
  using rvalue_reference  = value_type&&;

public:
  edgelist_iterator(graph_type& g, vertex_iterator ui, const EVF& value_fn)
        : base_type(), g_(g), ui_(ui), uvi_(), value_fn_(&value_fn) {}
  edgelist_iterator(graph_type& g, const EVF& value_fn) : edgelist_iterator(g, ranges::begin(vertices(g)), value_fn) {
    this->find_non_empty_vertex(g_, ui_, uvi_);
  }

  constexpr edgelist_iterator()                         = default;
  constexpr edgelist_iterator(const edgelist_iterator&) = default;
  constexpr edgelist_iterator(edgelist_iterator&&)      = default;
  constexpr ~edgelist_iterator()                        = default;

  constexpr edgelist_iterator& operator=(const edgelist_iterator&) = default;
  constexpr edgelist_iterator& operator=(edgelist_iterator&&)      = default;

protected:
  // avoid difficulty in undefined vertex reference value in value_type
  // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
  using shadow_edge_type = remove_reference_t<edge_reference_type>;
  using shadow_value_type =
        edge_descriptor<vertex_id_type, true, shadow_edge_type*, _detail::ref_to_ptr<edge_value_type>>;

public:
  constexpr reference operator*() const {
    if constexpr (unordered_edge<G, edge_type>) {
      if (target_id(g_, *uvi_) != vertex_id(g_, ui_)) {
        value_.source_id = source_id(g_, *uvi_);
        value_.target_id = target_id(g_, *uvi_);
      } else {
        value_.source_id = target_id(g_, *uvi_);
        value_.target_id = source_id(g_, *uvi_);
      }
      value_.edge  = &*uvi_;
      value_.value = invoke(*value_fn_, *uvi_);
    } else {
      value_ = {vertex_id(g_, ui_), target_id(g_, *uvi_), &*uvi_, invoke(*value_fn_, *uvi_)};
    }
    return reinterpret_cast<reference>(value_);
  }

  constexpr edgelist_iterator& operator++() {
    this->find_next_edge(g_, ui_, uvi_);
    return *this;
  }
  constexpr edgelist_iterator operator++(int) const {
    edgelist_iterator tmp(*this);
    ++*this;
    return tmp;
  }

  constexpr bool operator==(const edgelist_iterator& rhs) const { return uvi_ == rhs.uvi_; }
  //constexpr bool operator==(const edgelist_iterator& rhs) const { return uvi_ == rhs; }

private: // member variables
  mutable shadow_value_type        value_ = {};
  _detail::ref_to_ptr<graph_type&> g_;
  vertex_iterator                  ui_;
  edge_iterator                    uvi_;
  const EVF*                       value_fn_ = nullptr;

  friend bool operator==(const vertex_iterator& lhs, const edgelist_iterator& rhs) { return lhs == rhs.ui_; }
};


template <adjacency_list G>
class edgelist_iterator<G, void> : public edgelist_iterator_base<G> {
public:
  using base_type = edgelist_iterator_base<G>;

  using graph_type      = G;
  using vertex_type     = vertex_t<graph_type>;
  using vertex_id_type  = vertex_id_t<graph_type>;
  using vertex_iterator = vertex_iterator_t<G>;

  using edge_range          = vertex_edge_range_t<graph_type>;
  using edge_iterator       = vertex_edge_iterator_t<graph_type>;
  using edge_type           = edge_t<graph_type>;
  using edge_reference_type = edge_reference_t<graph_type>;
  using edge_value_type     = void;

  using iterator_category = forward_iterator_tag;
  using value_type        = edge_descriptor<const vertex_id_type, true, edge_reference_type, edge_value_type>;
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
  using shadow_value_type = edge_descriptor<vertex_id_type, true, shadow_edge_type*, edge_value_type>;

public:
  edgelist_iterator(graph_type& g, vertex_iterator ui) : base_type(), g_(g), ui_(ui), uvi_() {
    this->find_non_empty_vertex(g_, ui_, uvi_);
  }
  edgelist_iterator(graph_type& g) : edgelist_iterator(g, ranges::begin(vertices(g))) {}

  constexpr edgelist_iterator()                         = default;
  constexpr edgelist_iterator(const edgelist_iterator&) = default;
  constexpr edgelist_iterator(edgelist_iterator&&)      = default;
  constexpr ~edgelist_iterator()                        = default;

  constexpr edgelist_iterator& operator=(const edgelist_iterator&) = default;
  constexpr edgelist_iterator& operator=(edgelist_iterator&&)      = default;

public:
  constexpr reference operator*() const {
    if constexpr (unordered_edge<G, edge_type>) {
      if (target_id(g_, *uvi_) != vertex_id(g_, ui_)) {
        value_.source_id = source_id(g_, *uvi_);
        value_.target_id = target_id(g_, *uvi_);
      } else {
        value_.source_id = target_id(g_, *uvi_);
        value_.target_id = source_id(g_, *uvi_);
      }
      value_.edge = &*uvi_;
    } else {
      value_ = {vertex_id(g_, ui_), target_id(g_, *uvi_), &*uvi_};
    }
    return reinterpret_cast<reference>(value_);
  }

  constexpr edgelist_iterator& operator++() {
    this->find_next_edge(g_, ui_, uvi_);
    return *this;
  }
  constexpr edgelist_iterator operator++(int) const {
    edgelist_iterator tmp(*this);
    ++*this;
    return tmp;
  }

  constexpr bool operator==(const edgelist_iterator& rhs) const { return uvi_ == rhs.uvi_; }
  //constexpr bool operator==(const edgelist_iterator& rhs) const { return uvi_ == rhs; }

private: // member variables
  mutable shadow_value_type        value_ = {};
  _detail::ref_to_ptr<graph_type&> g_;
  vertex_iterator                  ui_;
  edge_iterator                    uvi_;

  friend bool operator==(const vertex_iterator& lhs, const edgelist_iterator& rhs) { return lhs == rhs.ui_; }
};


template <class G, class EVF>
using edgelist_view = ranges::subrange<edgelist_iterator<G, EVF>, vertex_iterator_t<G>>;


#if defined(NEW_CPO)

namespace std::graph::views {

  // edgelist(g)               -> edge_descriptor[uid,vid,uv]
  // edgelist(g,fn)            -> edge_descriptor[uid,vid,uv,value]
  // edgelist(g,uid,vid)       -> edge_descriptor[uid,vid,uv]
  // edgelist(g,uid,vid,fn)    -> edge_descriptor[uid,vid,uv,value]
  namespace _Edgelist {
#  if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
    void edgelist() = delete;                // Block unqualified name lookup
#  else                                      // ^^^ no workaround / workaround vvv
    void edgelist();
#  endif                                     // ^^^ workaround ^^^

    template <class G>
    concept _Has_all = _Has_class_or_enum_type<G> //
                       && requires(G&& g) {
                            { _Fake_copy_init(edgelist(g)) } -> ranges::forward_range;
                          };

    template <class G, class EVF>
    concept _Has_all_evf = _Has_class_or_enum_type<G>             //
                           && invocable<EVF, edge_reference_t<G>> //
                           && requires(G&& g, EVF& evf) {
                                { _Fake_copy_init(edgelist(g, evf)) } -> ranges::forward_range;
                              };

    template <class G>
    concept _Has_iter_rng = _Has_class_or_enum_type<G> //
                            && requires(G&& g, vertex_id_t<G> uid, vertex_id_t<G> vid) {
                                 { _Fake_copy_init(edgelist(g, uid, vid)) } -> ranges::forward_range;
                               };

    template <class G, class EVF>
    concept _Has_iter_rng_evf = _Has_class_or_enum_type<G>             //
                                && invocable<EVF, edge_reference_t<G>> //
                                && requires(G&& g, vertex_id_t<G> uid, vertex_id_t<G> vid, EVF& evf) {
                                     { _Fake_copy_init(edgelist(g, uid, vid, evf)) } -> ranges::forward_range;
                                   };

    class _Cpo {
    private:
      enum class _St_all_opt { _None, _Non_member };
      enum class _St_all_evf_opt { _None, _Non_member };
      enum class _St_iter_rng_opt { _None, _Non_member };
      enum class _St_iter_rng_evf_opt { _None, _Non_member };
      enum class _St_rng_opt { _None, _Non_member };
      enum class _St_rng_evf_opt { _None, _Non_member };

      template <class G>
      [[nodiscard]] static consteval _Choice_t<_St_all_opt> _Choose_all_opt() noexcept {
        if constexpr (_Has_all<G>) {
          return {_St_all_opt::_Non_member, noexcept(_Fake_copy_init(edgelist(declval<G>())))};
        } else {
          return {_St_all_opt::_None};
        }
      }
      template <class G>
      static constexpr _Choice_t<_St_all_opt> _Choice_all = _Choose_all_opt<G>();

      template <class G, class EVF>
      [[nodiscard]] static consteval _Choice_t<_St_all_evf_opt> _Choose_all_evf_opt() noexcept {
        if constexpr (_Has_all_evf<G, EVF>) {
          return _Choice_t<_St_all_evf_opt>{_St_all_evf_opt::_Non_member,
                                            noexcept(_Fake_copy_init(edgelist(declval<G>(), declval<EVF>())))};
        } else {
          return {_St_all_evf_opt::_None};
        }
      }
      template <class G, class EVF>
      static constexpr _Choice_t<_St_all_evf_opt> _Choice_all_evf = _Choose_all_evf_opt<G, EVF>();

      template <class G>
      [[nodiscard]] static consteval _Choice_t<_St_iter_rng_opt> _Choose_iter_rng_opt() noexcept {
        if constexpr (_Has_iter_rng<G>) {
          return {
                _St_iter_rng_opt::_Non_member,
                noexcept(_Fake_copy_init(edgelist(declval<G>(), //
                                                  declval<vertex_iterator_t<G>>(), declval<vertex_iterator_t<G>>())))};
        } else {
          return {_St_iter_rng_opt::_None};
        }
      }
      template <class G>
      static constexpr _Choice_t<_St_iter_rng_opt> _Choice_iter_rng = _Choose_iter_rng_opt<G>();

      template <class G, class EVF>
      [[nodiscard]] static consteval _Choice_t<_St_iter_rng_evf_opt> _Choose_iter_rng_evf_opt() noexcept {
        if constexpr (_Has_iter_rng_evf<G, EVF>) {
          return {_St_iter_rng_evf_opt::_Non_member,
                  noexcept(_Fake_copy_init(edgelist(declval<G>(),                    //
                                                    declval<vertex_iterator_t<G>>(), //
                                                    declval<vertex_iterator_t<G>>(), //
                                                    declval<EVF>())))};
        } else {
          return {_St_iter_rng_evf_opt::_None};
        }
      }
      template <class G>
      static constexpr _Choice_t<_St_iter_rng_evf_opt> _Choice_iter_rng_evf = _Choose_iter_rng_evf_opt<G>();


    public:
      /**
       * @brief Get a edgelist of a vertices in a graph.
       * 
       * Complexity: O(1)
       * 
       * Default implementation: returns edgelist_view<G>(vertices(std::forward<G>(g)))
       * 
       * @tparam G The graph type.
       * @param g A graph instance.
       * @return A range of all vertices with value_type of vertex_descriptor<vertex_id_t<G>, vertex_t<G>>.
      */
      template <class G>
      [[nodiscard]] constexpr auto operator()(G&& g) const noexcept(_Choice_all<G>._No_throw) {
        if constexpr (_Choice_all<G>()._Strategy == _St_all_opt::_Non_member) {
          return edgelist(forward<G>(g));
        } else {
          using iterator_type = edgelist_iterator<G, void>;
          return edgelist_view<G, void>(iterator_type(g), ranges::end(vertices(g)));
        }
      }

      /**
       * @brief Get a edgelist of all vertices in a graph with projected values.
       * 
       * Complexity: O(1)
       * 
       * Default implementation: returns edgelist_view<G>(vertices(std::forward<G>(g),value_fn))
       * 
       * @tparam G The graph type.
       * @param g A graph instance.
       * @param value_fn(edge_reference_t<G>) that returns a vertex value.
       * @return A range of all vertices with value_type of vertex_descriptor<vertex_id_t<G>, vertex_t<G>, decltype(value_fn())>.
      */
      template <class G, class EVF>
      requires invocable<EVF, edge_reference_t<G>>
      [[nodiscard]] constexpr auto operator()(G&& g, EVF&& evf) const noexcept(_Choice_all_evf<G, EVF>._No_throw) {
        if constexpr (_Choice_all_evf<G, EVF>()._Strategy == _St_all_opt::_Non_member) {
          return edgelist(forward<G>(g), evf);
        } else {
          using iterator_type = edgelist_iterator<G, EVF>;
          return edgelist_view<G, EVF>(iterator_type(g, evf), ranges::end(vertices(g)));
        }
      }

      /**
       * @brief Get the edgelist range for a graph for an interator range.
       * 
       * Complexity: O(1)
       * 
       * Default implementation: returns edgelist(g, first, last)
       * 
       * @tparam G The graph type.
       * @param g     A graph instance.
       * @param first First iterator in the vertex range.
       * @param last  Last iterator in the vertex range.
       * @return A range [first,last) of vertices with value_type of vertex_descriptor<vertex_id_t<G>, vertex_t<G>>.
      */
      template <class G>
      requires ranges::random_access_range<vertex_range_t<G>>
      [[nodiscard]] constexpr auto operator()(G&& g, vertex_iterator_t<G>& first, vertex_iterator_t<G>& last) const
            noexcept(_Choice_iter_rng<G&>._No_throw) {
        if constexpr (_Choice_iter_rng<G> == _St_iter_rng_opt::_Non_member) {
          return edgelist(forward(g), first, last);
        } else {
          using iterator_type = edgelist_iterator<G, void>;
          return edgelist_view<G, void>(iterator_type(g, find_vertex(g, first)), find_vertex(g, last));
        }
      }

      /**
       * @brief Get the edgelist range for a graph for an iterator range with projected values.
       * 
       * Complexity: O(1)
       * 
       * Default implementation: returns edgelist_view<G>(g, first, last, value_fn)
       * 
       * @tparam G The graph type.
       * @param g     A graph instance.
       * @param first First iterator in the vertex range.
       * @param last  Last iterator in the vertex range.
       * @return A range [first,last) of vertices with value_type of vertex_descriptor<vertex_id_t<G>, vertex_t<G>>.
      */
      template <class G, class EVF>
      requires ranges::random_access_range<vertex_range_t<G>> && invocable<EVF, edge_reference_t<G>>
      [[nodiscard]] constexpr auto
      operator()(G&& g, vertex_iterator_t<G>& first, vertex_iterator_t<G>& last, EVF&& evf) const
            noexcept(_Choice_iter_rng<G&>._No_throw) {
        if constexpr (_Choice_iter_rng_evf<G> == _St_iter_rng_evf_opt::_Non_member) {
          return edgelist(forward(g), first, last, evf);
        } else {
          using iterator_type = edgelist_iterator<G, EVF>;
          return edgelist_view<G, void>(iterator_type(g, find_vertex(g, first)), find_vertex(g, last), evf);
        }
      }
    };
  } // namespace _Edgelist

  inline namespace _Cpos {
    inline constexpr _Edgelist::_Cpo edgelist;
  }

} // namespace std::graph::views

#else  // defined(NEW_CPO)

namespace tag_invoke {
  // ranges
  TAG_INVOKE_DEF(edgelist); // edgelist(g)                 -> edges[uid,vid,uv]
                            // edgelist(g,fn)              -> edges[uid,vid,uv,value]
                            // edgelist(g,uid,vid)       -> edges[uid,vid,uv]
                            // edgelist(g,uid,vid,fn)    -> edges[uid,vid,uv,value]

  template <class G>
  concept _has_edgelist_g_adl = adjacency_list<G> && requires(G&& g) {
    { edgelist(g) };
  };
  template <class G>
  concept _has_edgelist_g_uid_adl = adjacency_list<G> && requires(G&& g, vertex_id_t<G> uid, vertex_id_t<G> vid) {
    { edgelist(g, uid, vid) };
  };
  template <class G, class EVF>
  concept _has_edgelist_g_evf_adl = adjacency_list<G> && requires(G&& g, const EVF& evf) {
    { edgelist(g, evf) };
  };
  template <class G, class EVF>
  concept _has_edgelist_g_uid_evf_adl =
        adjacency_list<G> && requires(G&& g, vertex_id_t<G> uid, vertex_id_t<G> vid, const EVF& evf) {
          { edgelist(g, uid, vid, evf) };
        };

} // namespace tag_invoke

//
// edgelist(g)
// edgelist(g,uid,vid)
//
template <adjacency_list G>
requires ranges::forward_range<vertex_range_t<G>>
constexpr auto edgelist(G&& g) {
  if constexpr (tag_invoke::_has_edgelist_g_adl<G>) {
    return tag_invoke::edgelist(g);
  } else {
    using iterator_type = edgelist_iterator<G, void>;
    return edgelist_view<G, void>(iterator_type(g), ranges::end(vertices(g)));
  }
}

template <adjacency_list G>
requires ranges::forward_range<vertex_range_t<G>>
constexpr auto edgelist(G&& g, vertex_id_t<G> first, vertex_id_t<G> last) {
  assert(first <= last && static_cast<size_t>(last) <= ranges::size(vertices(g)));
  if constexpr (tag_invoke::_has_edgelist_g_uid_adl<G>)
    return tag_invoke::edgelist(g, first, last);
  else {
    using iterator_type = edgelist_iterator<G, void>;
    return edgelist_view<G, void>(iterator_type(g, find_vertex(g, first)), find_vertex(g, last));
  }
}


//
// edgelist(g,u,evf)
// edgelist(g,uid,evf)
//
template <adjacency_list G, class EVF>
requires ranges::forward_range<vertex_range_t<G>>
constexpr auto edgelist(G&& g, const EVF& evf) {
  if constexpr (tag_invoke::_has_edgelist_g_evf_adl<G, EVF>) {
    return tag_invoke::edgelist(g, evf);
  } else {
    using iterator_type = edgelist_iterator<G, EVF>;
    return edgelist_view<G, EVF>(iterator_type(g, evf), ranges::end(vertices(g)));
  }
}

template <adjacency_list G, class EVF>
requires ranges::forward_range<vertex_range_t<G>>
constexpr auto edgelist(G&& g, vertex_id_t<G> first, vertex_id_t<G> last, const EVF& evf) {
  assert(first <= last && static_cast<size_t>(last) <= ranges::size(vertices(g)));
  if constexpr (tag_invoke::_has_edgelist_g_uid_evf_adl<G, EVF>)
    return tag_invoke::edgelist(g, first, last, evf);
  else {
    using iterator_type = edgelist_iterator<G, EVF>;
    return edgelist_view<G, void>(iterator_type(g, find_vertex(g, first)), find_vertex(g, last), evf);
  }
}


} // namespace std::graph::views

#endif // defined(NEW_CPO)
