//
//	Author: J. Phillip Ratzloff
//
// inspired by new_dfs_range.hpp from NWGraph
//
// depth-first search graph views for vertices and edges.
// All functions have an allocator parameter (not shown) for internally defined containers.
//
// examples: for(auto&& [vid,v]     : vertices_depth_first_search(g,seed))
//           for(auto&& [vid,v,val] : vertices_depth_first_search(g,seed,vvf))
//
//           for(auto&& [vid,uv]     : edges_depth_first_search(g,seed))
//           for(auto&& [vid,uv,val] : edges_depth_first_search(g,seed,evf))
//
//           for(auto&& [uid,vid,uv]     : sourced_edges_depth_first_search(g,seed))
//           for(auto&& [uid,vid,uv,val] : sourced_edges_depth_first_search(g,seed,evf))
//
// Given dfs is one of the depth-first views above, the following functions are also available.
//
//  size(dfs) returns the depth of the current search (the size of the internal stack)
//
//  dfs.cancel(cancel_search::cancel_branch) will stop searching from the current vertex
//  dfs.cancel(cancel_search::cancel_all) will stop searching and the iterator will be at the end()
//

#include "graph/graph.hpp"
#include "graph/graph_utility.hpp"
#include <stack>
#include <vector>
#include <functional>

#ifndef GRAPH_DFS_HPP
#  define GRAPH_DFS_HPP

namespace std::graph {

/**
 * @brief The element in a depth-first search stack.
*/
template <adjacency_list G>
struct dfs_element {
  vertex_id_t<G>            u_id;
  vertex_edge_iterator_t<G> uv;
};

/**
 * @brief Depth-first search view for vertices, given a single seed vertex.
 * 
 * @tparam G     Graph type
 * @tparam Stack Stack type for internal use
 * @tparam Alloc Allocator type
*/
template <adjacency_list G, class Stack, class Alloc>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>>
class dfs_base : public ranges::view_base {
public:
  using graph_type       = G;
  using vertex_type      = vertex_t<G>;
  using vertex_id_type   = vertex_id_t<graph_type>;
  using vertex_reference = vertex_reference_t<graph_type>;
  using vertex_iterator  = vertex_iterator_t<graph_type>;
  using edge_type        = edge_t<G>;
  using edge_reference   = edge_reference_t<G>;
  using edge_iterator    = vertex_edge_iterator_t<graph_type>;

private:
  using graph_ref_type = reference_wrapper<graph_type>;
  using stack_elem     = dfs_element<graph_type>;

  using parent_alloc = typename allocator_traits<typename Stack::container_type::allocator_type>::template rebind_alloc<
        vertex_id_type>;

public:
  dfs_base(graph_type& g, vertex_id_type seed, const Alloc& alloc)
        : graph_(g), S_(alloc), colors_(ranges::size(vertices(g)), white, alloc) {
    if (seed < static_cast<vertex_id_type>(ranges::size(vertices(graph_))) && !ranges::empty(edges(graph_, seed))) {
      edge_iterator uvi = ranges::begin(edges(graph_, seed));
      S_.push(stack_elem{seed, uvi});
      colors_[seed] = grey;

      // Mark initial vertex as visited
      if (uvi != ranges::end(edges(graph_, seed))) {
        vertex_id_type v_id = real_target_id(*uvi, seed);
        colors_[v_id]       = grey;
      }
    }
  }
  dfs_base()                = default;
  dfs_base(const dfs_base&) = delete; // can be expensive to copy
  dfs_base(dfs_base&&)      = default;
  ~dfs_base()               = default;

  dfs_base& operator=(const dfs_base&) = delete;
  dfs_base& operator=(dfs_base&&)      = default;

  constexpr bool empty() const noexcept { return S_.empty(); }

  constexpr auto size() const noexcept { return S_.size(); }
  constexpr auto depth() const noexcept { return S_.size(); }

  constexpr void          cancel(cancel_search cancel_type) noexcept { cancel_ = cancel_type; }
  constexpr cancel_search canceled() noexcept { return cancel_; }

protected:
  constexpr vertex_id_type real_target_id(edge_reference uv, vertex_id_type) const
  requires ordered_edge<G, edge_type>
  {
    return target_id(graph_, uv);
  }
  constexpr vertex_id_type real_target_id(edge_reference uv, vertex_id_type src) const
  requires unordered_edge<G, edge_type>
  {
    if (target_id(graph_, uv) != src)
      return target_id(graph_, uv);
    else
      return source_id((graph_), uv);
  }

  constexpr vertex_edge_iterator_t<G> find_unvisited(vertex_id_t<G> uid, vertex_edge_iterator_t<G> first) {
    return ranges::find_if(first, ranges::end(edges(graph_, uid)), [this, uid](edge_reference uv) -> bool {
      return colors_[real_target_id(uv, uid)] == white;
    });
  }

  constexpr void advance() {
    // next level in search
    auto [u_id, uvi]    = S_.top();
    vertex_id_type v_id = real_target_id(*uvi, u_id);

    edge_iterator vwi = ranges::end(edges(graph_, v_id));
    switch (cancel_) {
    case cancel_search::continue_search:
      // find first unvisited edge of v
      vwi = find_unvisited(v_id, ranges::begin(edges(graph_, v_id)));
      break;
    case cancel_search::cancel_branch: {
      cancel_       = cancel_search::continue_search;
      colors_[v_id] = black; // finished with v

      // Continue with sibling?
      uvi = find_unvisited(u_id, ++uvi);
      if (uvi != ranges::end(edges(graph_, u_id))) {
        S_.top().uv = uvi;
        return;
      }
      // drop thru to unwind the stack to the parent
    } break;
    case cancel_search::cancel_all:
      while (!S_.empty())
        S_.pop();
      return;
    }

    // unvisited edge found for vertex v?
    if (vwi != ranges::end(edges(graph_, v_id))) {
      S_.push(stack_elem{v_id, vwi});
      vertex_id_type w_id = real_target_id(*vwi, v_id);
      colors_[w_id]       = grey; // visited w
    }
    // we've reached the end of a branch in the DFS tree; start unwinding the stack to find other unvisited branches
    else {
      colors_[v_id] = black; // finished with v
      S_.pop();
      while (!S_.empty()) {
        auto [x_id, xyi] = S_.top();
        S_.pop();
        xyi = find_unvisited(x_id, ++xyi);

        // unvisted edge found for vertex x?
        if (xyi != ranges::end(edges(graph_, x_id))) {
          S_.push({x_id, xyi});
          vertex_id_type y_id = real_target_id(*xyi, x_id);
          colors_[y_id]       = grey; // visited y
          break;
        } else {
          colors_[x_id] = black; // finished with x
        }
      }
    }
  }

protected:
  _detail::ref_to_ptr<graph_type&> graph_;
  Stack                            S_;
  vector<three_colors>             colors_;
  cancel_search                    cancel_ = cancel_search::continue_search;
};


/**
 * @brief Depth-first search range for vertices, given a single seed vertex.
 * 
 * @tparam G     Graph type
 * @tparam VVF   Vertex Value Function type
 * @tparam Stack Stack type for internal use
 * @tparam Alloc Allocator type
*/
template <adjacency_list G, class VVF = void, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>>
class vertices_depth_first_search_view : public dfs_base<G, Stack, Alloc> {
public:
  using base_type        = dfs_base<G, Stack, Alloc>;
  using graph_type       = G;
  using vertex_type      = vertex_t<G>;
  using vertex_id_type   = vertex_id_t<graph_type>;
  using vertex_reference = vertex_reference_t<graph_type>;
  using vertex_iterator  = vertex_iterator_t<graph_type>;
  using edge_reference   = edge_reference_t<G>;
  using edge_iterator    = vertex_edge_iterator_t<graph_type>;
  using dfs_range_type   = vertices_depth_first_search_view<graph_type, VVF, Stack, Alloc>;

  using vertex_value_func = VVF;
  using vertex_value_type = invoke_result_t<VVF, vertex_reference>;

public:
  vertices_depth_first_search_view(graph_type&    g,
                                   vertex_id_type seed,
                                   const VVF&     value_fn,
                                   const Alloc&   alloc = Alloc())
        : base_type(g, seed, alloc), value_fn_(&value_fn) {}
  vertices_depth_first_search_view()                                        = default;
  vertices_depth_first_search_view(const vertices_depth_first_search_view&) = delete; // can be expensive to copy
  vertices_depth_first_search_view(vertices_depth_first_search_view&&)      = default;
  ~vertices_depth_first_search_view()                                       = default;

  vertices_depth_first_search_view& operator=(const vertices_depth_first_search_view&) = delete;
  vertices_depth_first_search_view& operator=(vertices_depth_first_search_view&&)      = default;

public:
  class iterator;
  struct end_sentinel {
    constexpr bool operator==(const iterator& rhs) const noexcept { return rhs.the_range_->S_.empty(); }
    //constexpr bool operator!=(const iterator& rhs) const noexcept { return !operator==(rhs); }
  };

  class iterator {
  public:
    using iterator_category = input_iterator_tag;
    using value_type        = vertex_descriptor<const vertex_id_type, vertex_type&, vertex_value_type>;
    using reference         = value_type&;
    using const_reference   = const value_type&;
    using rvalue_reference  = value_type&&;
    using pointer           = value_type*;
    using const_pointer     = value_type*;
    using size_type         = ranges::range_size_t<vertex_range_t<graph_type>>;
    using difference_type   = ranges::range_difference_t<vertex_range_t<graph_type>>;

  private:
    // use of shadow_vertex_type avoids difficulty in undefined vertex reference value in value_type
    // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
    using shadow_vertex_type = remove_reference_t<vertex_reference>;
    using shadow_value_type =
          vertex_descriptor<vertex_id_t<graph_type>, shadow_vertex_type*, _detail::ref_to_ptr<vertex_value_type>>;

  public:
    iterator(const dfs_range_type& range) : the_range_(&const_cast<dfs_range_type&>(range)) {}
    iterator()                = default;
    iterator(const iterator&) = default;
    iterator(iterator&&)      = default;
    ~iterator()               = default;

    iterator& operator=(const iterator&) = default;
    iterator& operator=(iterator&&)      = default;

    iterator& operator++() {
      the_range_->advance();
      return *this;
    }
    iterator operator++(int) const {
      iterator temp(*this);
      ++*this;
      return temp;
    }

    reference operator*() const noexcept {
      auto& g             = the_range_->graph_;
      auto&& [u_id, uvi]  = the_range_->S_.top();
      vertex_id_type v_id = the_range_->real_target_id(*uvi, u_id);
      auto&          v    = *find_vertex(g, v_id);
      value_              = {v_id, &v, invoke(*the_range_->value_fn_, v)};
      return reinterpret_cast<reference>(value_);
    }

    constexpr bool operator==(const end_sentinel&) const noexcept { return the_range_->S_.empty(); }
    //constexpr bool operator!=(const end_sentinel& rhs) const noexcept { return !operator==(rhs); }

  private:
    mutable shadow_value_type value_     = {};
    dfs_range_type*           the_range_ = nullptr;
    friend end_sentinel;
  };

  auto begin() { return iterator(*this); }
  auto begin() const { return iterator(*this); }
  auto cbegin() const { return iterator(*this); }

  auto end() { return end_sentinel(); }
  auto end() const { return end_sentinel(); }
  auto cend() const { return end_sentinel(); }

private:
  const VVF* value_fn_ = nullptr;
};


template <adjacency_list G, class Stack, class Alloc>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>>
class vertices_depth_first_search_view<G, void, Stack, Alloc> : public dfs_base<G, Stack, Alloc> {
public:
  using base_type        = dfs_base<G, Stack, Alloc>;
  using graph_type       = G;
  using vertex_type      = vertex_t<G>;
  using vertex_id_type   = vertex_id_t<graph_type>;
  using vertex_reference = vertex_reference_t<graph_type>;
  using vertex_iterator  = vertex_iterator_t<graph_type>;
  using edge_reference   = edge_reference_t<G>;
  using edge_iterator    = vertex_edge_iterator_t<graph_type>;
  using dfs_range_type   = vertices_depth_first_search_view<graph_type, void, Stack, Alloc>;

public:
  vertices_depth_first_search_view(graph_type& g, vertex_id_type seed, const Alloc& alloc = Alloc())
        : base_type(g, seed, alloc) {}
  vertices_depth_first_search_view()                                        = default;
  vertices_depth_first_search_view(const vertices_depth_first_search_view&) = delete; // can be expensive to copy
  vertices_depth_first_search_view(vertices_depth_first_search_view&&)      = default;
  ~vertices_depth_first_search_view()                                       = default;

  vertices_depth_first_search_view& operator=(const vertices_depth_first_search_view&) = delete;
  vertices_depth_first_search_view& operator=(vertices_depth_first_search_view&&)      = default;

public:
  struct end_sentinel {
    bool operator==(const end_sentinel& rhs) const noexcept { return rhs.the_range_->S_.empty(); }
  };

  class iterator {
  public:
    using iterator_category = input_iterator_tag;
    using value_type        = vertex_descriptor<const vertex_id_type, vertex_type&, void>;
    using reference         = value_type&;
    using const_reference   = const value_type&;
    using rvalue_reference  = value_type&&;
    using pointer           = value_type*;
    using const_pointer     = value_type*;
    using size_type         = ranges::range_size_t<vertex_range_t<graph_type>>;
    using difference_type   = ranges::range_difference_t<vertex_range_t<graph_type>>;

  private:
    // use of shadow_vertex_type avoids difficulty in undefined vertex reference value in value_type
    // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
    using shadow_vertex_type = remove_reference_t<vertex_reference>;
    using shadow_value_type  = vertex_descriptor<vertex_id_t<graph_type>, shadow_vertex_type*, void>;

  public:
    iterator(const dfs_range_type& range) : the_range_(&const_cast<dfs_range_type&>(range)) {}
    iterator()                = default;
    iterator(const iterator&) = default;
    iterator(iterator&&)      = default;
    ~iterator()               = default;

    iterator& operator=(const iterator&) = default;
    iterator& operator=(iterator&&)      = default;

    iterator& operator++() {
      the_range_->advance();
      return *this;
    }
    iterator operator++(int) const {
      iterator temp(*this);
      ++*this;
      return temp;
    }

    reference operator*() const noexcept {
      auto& g             = the_range_->graph_;
      auto&& [u_id, uvi]  = the_range_->S_.top();
      vertex_id_type v_id = the_range_->real_target_id(*uvi, u_id);
      auto&          v    = *find_vertex(g, v_id);
      value_              = {v_id, &v};
      return reinterpret_cast<reference>(value_);
    }

    bool operator==(const end_sentinel&) const noexcept { return the_range_->S_.empty(); }
    //bool operator!=(const end_sentinel& rhs) const noexcept { return !operator==(rhs); }

  private:
    mutable shadow_value_type value_     = {};
    dfs_range_type*           the_range_ = nullptr;
    friend end_sentinel;
  };

  auto begin() { return iterator(*this); }
  auto begin() const { return iterator(*this); }
  auto cbegin() const { return iterator(*this); }

  auto end() { return end_sentinel{}; }
  auto end() const { return end_sentinel{}; }
  auto cend() const { return end_sentinel{}; }
};


/**
 * @brief Depth-first search view for edges, given a single seed vertex.
 * 
 * @tparam G       Graph type
 * @tparam EVF     Edge Value Function type
 * @tparam Sourced Does graph G support @c source_id()?
 * @tparam Stack   Stack type for use internally
 * @tparam Alloc   Allocator type
*/
template <adjacency_list G,
          class EVF    = void,
          bool Sourced = false,
          class Stack  = stack<dfs_element<G>>,
          class Alloc  = allocator<bool>>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>>
class edges_depth_first_search_view : public dfs_base<G, Stack, Alloc> {
public:
  using base_type           = dfs_base<G, Stack, Alloc>;
  using graph_type          = G;
  using vertex_id_type      = vertex_id_t<graph_type>;
  using vertex_iterator     = vertex_iterator_t<graph_type>;
  using edge_reference_type = edge_reference_t<graph_type>;
  using dfs_range_type      = edges_depth_first_search_view<G, EVF, Sourced, Stack, Alloc>;

  using edge_value_func = EVF;
  using edge_value_type = invoke_result_t<EVF, edge_reference_type>;

public:
  edges_depth_first_search_view(G& g, vertex_id_type seed, const EVF& value_fn, const Alloc& alloc = Alloc())
        : base_type(g, seed, alloc), value_fn_(&value_fn) {}

  edges_depth_first_search_view()                                     = default;
  edges_depth_first_search_view(const edges_depth_first_search_view&) = delete; // can be expensive to copy
  edges_depth_first_search_view(edges_depth_first_search_view&&)      = default;
  ~edges_depth_first_search_view()                                    = default;

  edges_depth_first_search_view& operator=(const edges_depth_first_search_view&) = delete;
  edges_depth_first_search_view& operator=(edges_depth_first_search_view&&)      = default;

  class iterator;
  struct end_sentinel {
    constexpr bool operator==(const iterator& rhs) const noexcept { return rhs.the_range_->S_.empty(); }
    //constexpr bool operator!=(const iterator& rhs) const noexcept { return !operator==(rhs); }
  };

  class iterator {
  public:
    using iterator_category = input_iterator_tag;
    using value_type        = edge_descriptor<const vertex_id_type, Sourced, edge_reference_type, edge_value_type>;
    using reference         = value_type&;
    using const_reference   = const value_type&;
    using rvalue_reference  = value_type&&;
    using pointer           = value_type*;
    using const_pointer     = value_type*;
    using size_type         = ranges::range_size_t<vertex_range_t<graph_type>>;
    using difference_type   = ranges::range_difference_t<vertex_range_t<graph_type>>;

  private:
    // avoid difficulty in undefined vertex reference value in value_type
    // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
    using shadow_edge_type = remove_reference_t<edge_reference_type>;
    using shadow_value_type =
          edge_descriptor<vertex_id_type, Sourced, shadow_edge_type*, _detail::ref_to_ptr<edge_value_type>>;

  public:
    iterator(const dfs_range_type& range) : the_range_(&const_cast<dfs_range_type&>(range)) {}
    iterator()                = default;
    iterator(const iterator&) = default;
    iterator(iterator&&)      = default;
    ~iterator()               = default;

    iterator& operator=(const iterator&) = default;
    iterator& operator=(iterator&&)      = default;

    iterator& operator++() {
      the_range_->advance();
      return *this;
    }
    iterator operator++(int) const {
      iterator temp(*this);
      ++*this;
      return temp;
    }

    reference operator*() const noexcept {
      auto&& [u_id, uvi] = the_range_->S_.top();
      if constexpr (Sourced) {
        value_.source_id = u_id;
      }
      value_.target_id = the_range_->real_target_id(*uvi, u_id);
      value_.edge      = &*uvi;
      value_.value     = invoke(*the_range_->value_fn_, *uvi);
      return reinterpret_cast<reference>(value_);
    }

    bool operator==(const end_sentinel&) const noexcept { return the_range_->S_.empty(); }
    //bool operator!=(const end_sentinel& rhs) const noexcept { return !operator==(rhs); }

  private:
    mutable shadow_value_type value_     = {};
    dfs_range_type*           the_range_ = nullptr;
    friend end_sentinel;
  };

  auto begin() { return iterator(*this); }
  auto begin() const { return iterator(*this); }
  auto cbegin() const { return iterator(*this); }

  auto end() { return end_sentinel(); }
  auto end() const { return end_sentinel(); }
  auto cend() const { return end_sentinel(); }

private:
  const EVF* value_fn_ = nullptr;
};

template <adjacency_list G, bool Sourced, class Stack, class Alloc>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>>
class edges_depth_first_search_view<G, void, Sourced, Stack, Alloc> : public dfs_base<G, Stack, Alloc> {
public:
  using base_type           = dfs_base<G, Stack, Alloc>;
  using graph_type          = G;
  using vertex_id_type      = vertex_id_t<graph_type>;
  using vertex_iterator     = vertex_iterator_t<graph_type>;
  using edge_reference_type = edge_reference_t<graph_type>;
  using dfs_range_type      = edges_depth_first_search_view<G, void, Sourced, Stack, Alloc>;

public:
  edges_depth_first_search_view(G& g, vertex_id_type seed, const Alloc& alloc = Alloc()) : base_type(g, seed, alloc) {}

  edges_depth_first_search_view()                                     = default;
  edges_depth_first_search_view(const edges_depth_first_search_view&) = delete; // can be expensive to copy
  edges_depth_first_search_view(edges_depth_first_search_view&&)      = default;
  ~edges_depth_first_search_view()                                    = default;

  edges_depth_first_search_view& operator=(const edges_depth_first_search_view&) = delete;
  edges_depth_first_search_view& operator=(edges_depth_first_search_view&&)      = default;

  class iterator;
  struct end_sentinel {
    bool operator==(const end_sentinel& rhs) const noexcept { return rhs.the_range_->S_.empty(); }
    //bool operator!=(const end_sentinel& rhs) const noexcept { return !operator==(rhs); }
  };

  class iterator {
  public:
    using iterator_category = input_iterator_tag;
    using value_type        = edge_descriptor<const vertex_id_type, Sourced, edge_reference_type, void>;
    using reference         = value_type&;
    using const_reference   = const value_type&;
    using rvalue_reference  = value_type&&;
    using pointer           = value_type*;
    using const_pointer     = value_type*;
    using size_type         = ranges::range_size_t<vertex_range_t<graph_type>>;
    using difference_type   = ranges::range_difference_t<vertex_range_t<graph_type>>;

  private:
    // avoid difficulty in undefined vertex reference value in value_type
    // shadow_vertex_value_type: ptr if vertex_value_type is ref or ptr, value otherwise
    using shadow_edge_type  = remove_reference_t<edge_reference_type>;
    using shadow_value_type = edge_descriptor<vertex_id_type, Sourced, shadow_edge_type*, void>;

  public:
    iterator(const dfs_range_type& range) : the_range_(&const_cast<dfs_range_type&>(range)) {}
    iterator()                = default;
    iterator(const iterator&) = default;
    iterator(iterator&&)      = default;
    ~iterator()               = default;

    iterator& operator=(const iterator&) = default;
    iterator& operator=(iterator&&)      = default;

    iterator& operator++() {
      the_range_->advance();
      return *this;
    }
    iterator operator++(int) const {
      iterator temp(*this);
      ++*this;
      return temp;
    }

    reference operator*() const noexcept {
      auto&& [u_id, uvi] = the_range_->S_.top();
      if constexpr (Sourced) {
        value_.source_id = u_id;
      }
      value_.target_id = the_range_->real_target_id(*uvi, u_id);
      value_.edge      = &*uvi;
      return reinterpret_cast<reference>(value_);
    }

    bool operator==(const end_sentinel&) const noexcept { return the_range_->S_.empty(); }
    //bool operator!=(const end_sentinel& rhs) const noexcept { return !operator==(rhs); }

  private:
    mutable shadow_value_type value_     = {};
    dfs_range_type*           the_range_ = nullptr;
    friend end_sentinel;
  };

  auto begin() { return iterator(*this); }
  auto begin() const { return iterator(*this); }
  auto cbegin() const { return iterator(*this); }

  auto end() { return end_sentinel(); }
  auto end() const { return end_sentinel(); }
  auto cend() const { return end_sentinel(); }
};
} // namespace std::graph


#  ifdef NEW_CPO

namespace std::graph::views {

// vertices_depth_first_search(g,seed,alloc)    -> vertex_descriptor[uid,u]
// vertices_depth_first_search(g,seed,fn,alloc) -> vertex_descriptor[uid,u,value]
namespace _Vertices_depth_first_search {
#    if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void vertices_depth_first_search() = delete; // Block unqualified name lookup
#    else                                      // ^^^ no workaround / workaround vvv
  void vertices_depth_first_search();
#    endif                                     // ^^^ workaround ^^^

  template <class G, class Alloc>
  concept _Has_all = _Has_class_or_enum_type<G> //
                     && requires(G&& g, vertex_id_t<G> seed, Alloc& alloc) {
                          { _Fake_copy_init(vertices_depth_first_search(g, seed, alloc)) } -> ranges::forward_range;
                        };

  template <class G, class VVF, class Alloc>
  concept _Has_all_vvf = _Has_class_or_enum_type<G> //
                         && requires(G&& g, vertex_id_t<G> seed, VVF& vvf, Alloc& alloc) {
                              {
                                _Fake_copy_init(vertices_depth_first_search(g, seed, vvf, alloc))
                              } -> ranges::forward_range;
                            };

  class _Cpo {
  private:
    enum class _St_all_opt { _None, _Non_member };
    enum class _St_all_vvf_opt { _None, _Non_member };

    template <class G, class Alloc>
    [[nodiscard]] static consteval _Choice_t<_St_all_opt> _Choose_all_opt() noexcept {
      if constexpr (_Has_all<G>) {
        return {_St_all_opt::_Non_member, noexcept(_Fake_copy_init(vertices_depth_first_search(
                                                declval<G>(), declval<vertex_id_t<G>>(), declval<Alloc>())))};
      } else {
        return {_St_all_opt::_None};
      }
    }
    template <class G, class Alloc>
    static constexpr _Choice_t<_St_all_opt> _Choice_all = _Choose_all_opt<G, Alloc>();

    template <class G, class VVF, class Alloc>
    [[nodiscard]] static consteval _Choice_t<_St_all_vvf_opt> _Choose_all_vvf_opt() noexcept {
      if constexpr (_Has_all_vvf<G, VVF, Alloc>) {
        return {_St_all_vvf_opt::_Non_member,
                noexcept(_Fake_copy_init(vertices_depth_first_search(std::declval<G>(), declval<vertex_id_t<G>>(),
                                                                     declval<VVF>(), declval<Alloc>())))};
      } else {
        return {_St_all_vvf_opt::_None};
      }
    }
    template <class G, class VVF, class Alloc>
    static constexpr _Choice_t<_St_all_vvf_opt> _Choice_all_vvf = _Choose_all_vvf_opt<G, VVF, Alloc>();

  public:
    /**
     * @brief Get a vertices_depth_first_search of a vertices in a graph.
     * 
     * Complexity: O(N)
     * 
     * Default implementation: vertices_depth_first_search_view<G>(vertices(g))
     * 
     * @tparam G     The graph type.
     * @tparam Stack Stack type (used internally)
     * @tparam Alloc Allocator type
     * 
     * @param g        A graph instance.
     * @param seed     Vertex id to start the search.
     * @param alloc    Allocator used for internal storage
     * 
     * @return A range of all vertices with value_type of vertex_descriptor<vertex_id_t<G>, vertex_t<G>>.
    */
    template <adjacency_list G, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
    [[nodiscard]] constexpr auto operator()(G&& g, vertex_id_t<G>&& seed, const Alloc& alloc = Alloc()) const
          noexcept(_Choice_all<G, Alloc>._No_throw) {
      if constexpr (_Choice_all<G, Alloc>()._Strategy == _St_all_opt::_Non_member) {
        return vertices_depth_first_search(std::forward<G>(g), std::forward<decltype(seed)>(seed), alloc);
      } else {
        return vertices_depth_first_search_view<G, Stack>( //
              std::forward<decltype(g)>(g),                //
              std::forward<decltype(seed)>(seed),          //
              alloc);
      }
    }

    /**
     * @brief Get a vertices_depth_first_search of all vertices in a graph with projected values.
     * 
     * Complexity: O(N)
     * 
     * Default implementation: vertices_depth_first_search_view<G,VVF,Stack>(vertices(g,vvf))
     * 
     * @tparam G     The graph type.
     * @tparam VVF   Edge Value Function
     * @tparam Stack Stack type (used internally)
     * @tparam Alloc Allocator type
     * 
     * @param g      A graph instance.
     * @param seed   Vertex id to start the search.
     * @param vvf    Function that takes a vertex reference and returns a vertex value.
     * @param alloc  Allocator used for internal storage
     * 
     * @return A range of all vertices with value_type of vertex_descriptor<vertex_id_t<G>, vertex_t<G>, decltype(vvf())>.
    */
    template <adjacency_list G, class VVF, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
    requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> &&
             invocable<VVF, vertex_t<G>> && _detail::is_allocator_v<Alloc>
    [[nodiscard]] constexpr auto operator()(G&& g, vertex_id_t<G>&& seed, VVF&& vvf, const Alloc& alloc = Alloc()) const
          noexcept(_Choice_all_vvf<G, VVF, Alloc>._No_throw) {
      if constexpr (_Choice_all_vvf<G, VVF, Alloc>()._Strategy == _St_all_opt::_Non_member) {
        return vertices_depth_first_search(std::forward<G>(g), std::forward<decltype(seed)>(seed),
                                           std::forward<decltype(vvf)>(vvf), alloc);
      } else {
        return vertices_depth_first_search_view<G, VVF, Stack>( //
              std::forward<decltype(g)>(g),                     //
              std::forward<decltype(seed)>(seed),               //
              std::forward<decltype(vvf)>(vvf),                 //
              alloc);
      }
    }
  };
} // namespace _Vertices_depth_first_search

inline namespace _Cpos {
  inline constexpr _Vertices_depth_first_search::_Cpo vertices_depth_first_search;
}


//
// edges_depth_first_search(g,seed,alloc)
// edges_depth_first_search(g,seed,evf,alloc)
//
namespace _Edges_depth_first_search {
  template <class G, class Alloc>
  concept _Has_all = _Has_class_or_enum_type<G> //
                     && requires(G&& g, vertex_id_t<G> seed, Alloc alloc) {
                          { _Fake_copy_init(edges_depth_first_search(g, seed, alloc)) } -> ranges::forward_range;
                        };

  template <class G, class EVF, class Alloc>
  concept _Has_all_evf = _Has_class_or_enum_type<G>             //
                         && invocable<EVF, edge_reference_t<G>> //
                         && requires(G&& g, vertex_id_t<G> seed, EVF evf, Alloc alloc) {
                              {
                                _Fake_copy_init(edges_depth_first_search(g, seed, evf, alloc))
                              } -> ranges::forward_range;
                            };

  class _Cpo {
  private:
    enum class _St_all_opt { _None, _Non_member };
    enum class _St_all_evf_opt { _None, _Non_member };

    template <class G, class Alloc>
    [[nodiscard]] static consteval _Choice_t<_St_all_opt> _Choose_all_opt() noexcept {
      if constexpr (_Has_all<G>) {
        return {_St_all_opt::_Non_member, noexcept(_Fake_copy_init(edges_depth_first_search(
                                                declval<G>(), declval<vertex_id_t<G>>(), declval<Alloc>())))};
      } else {
        return {_St_all_opt::_None};
      }
    }
    template <class G, class Alloc>
    static constexpr _Choice_t<_St_all_opt> _Choice_all = _Choose_all_opt<G, Alloc>();

    template <class G, class EVF, class Alloc>
    [[nodiscard]] static consteval _Choice_t<_St_all_evf_opt> _Choose_all_evf_opt() noexcept {
      if constexpr (_Has_all_evf<G>) {
        return {_St_all_evf_opt::_Non_member,
                noexcept(_Fake_copy_init(edges_depth_first_search(std::declval<G>(), declval<vertex_id_t<G>>(),
                                                                  std::declval<EVF>(), std::declval<Alloc>())))};
      } else {
        return {_St_all_evf_opt::_None};
      }
    }
    template <class G, class EVF, class Alloc>
    static constexpr _Choice_t<_St_all_evf_opt> _Choice_all_evf = _Choose_all_evf_opt<G, EVF, Alloc>();

  public:
    /**
     * @brief Get edges of a seed vertex recursively, in depth-first order.
     * 
     * Complexity: O(N)
     * 
     * Default implementation: edges_depth_first_search_view<G, void, false, Stack>(g, seed, alloc);
     * 
     * @tparam G     The graph type.
     * @tparam Stack Stack type (used internally)
     * @tparam Alloc Allocator type
     * 
     * @param g     A graph instance.
     * @param seed  Vertex id to get the outgoing edges for.
     * @param alloc Allocator used for internal storage
     * 
     * @return The range of outgoing edges on a vertex with value_type of edge_descriptor<vertex_id_t<G>, false, edge_reference_t<G>>.
    */
    template <adjacency_list G, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
    requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> &&
             _detail::is_allocator_v<Alloc>
    [[nodiscard]] constexpr auto operator()(G&& g, vertex_id_t<G>&& seed, const Alloc& alloc = Alloc()) const
          noexcept(_Choice_all<G, Alloc>._No_throw) {
      if constexpr (_Choice_all<G, Alloc>()._Strategy == _St_all_opt::_Non_member) {
        return edges_depth_first_search(forward<decltype(g)>(g),       //
                                        forward<decltype(seed)>(seed), //
                                        alloc);
      } else {
        return edges_depth_first_search_view<G, void, false, Stack>(forward<decltype(g)>(g),       //
                                                                    forward<decltype(seed)>(seed), //
                                                                    alloc);
      }
    }

    /**
     * @brief Get edges of a seed vertex recursively with projected values, in depth-first order.
     * 
     * Complexity: O(N)
     * 
     * Default implementation: edges_depth_first_search_view<G, EVF, false, Stack>(g, seed, evf, alloc);
     * 
     * @tparam G     The graph type.
     * @tparam EVF   Edge Value Function
     * @tparam Stack Stack type (used internally)
     * @tparam Alloc Allocator type
     * 
     * @param g      A graph instance.
     * @param seed   Vertex id to get the outgoing edges for.
     * @param evf    Function that takes an edge reference and returns an edge value.
     * @param alloc  Allocator used for internal storage
     * 
     * @return The range of all outgoing edges of a vertex with value_type of edge_descriptor<vertex_id_t<G>, false, edge_reference<G>, decltype(evf())>.
    */
    template <adjacency_list G, class EVF, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
    requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> &&
             invocable<EVF, edge_reference_t<G>> && _detail::is_allocator_v<Alloc>
    [[nodiscard]] constexpr auto operator()(G&& g, vertex_id_t<G>&& seed, EVF&& evf, const Alloc& alloc = Alloc()) const
          noexcept(_Choice_all_evf<G, EVF, Alloc>._No_throw) {
      if constexpr (_Choice_all_evf<G, EVF, Alloc>()._Strategy == _St_all_opt::_Non_member) {
        return edges_depth_first_search(forward<decltype(g)>(g),       //
                                        forward<decltype(seed)>(seed), //
                                        forward<decltype(evf)>(evf),   //
                                        alloc);
      } else {
        return edges_depth_first_search_view<G, EVF, false, Stack>(forward<decltype(g)>(g),       //
                                                                   forward<decltype(seed)>(seed), //
                                                                   forward<decltype(evf)>(evf),   //
                                                                   alloc);
      }
    }
  };

} // namespace _Edges_depth_first_search

inline namespace _Cpos {
  inline constexpr _Edges_depth_first_search::_Cpo edges_depth_first_search;
}

//
// sourced_edges_depth_first_search(g,seed,alloc)
// sourced_edges_depth_first_search(g,seed,evf,alloc)
//
namespace _Sourced_edges_depth_first_search {
  template <class G, class Alloc>
  concept _Has_all = _Has_class_or_enum_type<G> //
                     && requires(G&& g, vertex_id_t<G> seed, Alloc alloc) {
                          {
                            _Fake_copy_init(sourced_edges_depth_first_search(g, seed, alloc))
                          } -> ranges::forward_range;
                        };

  template <class G, class EVF, class Alloc>
  concept _Has_all_evf = _Has_class_or_enum_type<G>             //
                         && invocable<EVF, edge_reference_t<G>> //
                         && requires(G&& g, vertex_id_t<G> seed, EVF evf, Alloc alloc) {
                              {
                                _Fake_copy_init(sourced_edges_depth_first_search(g, seed, evf, alloc))
                              } -> ranges::forward_range;
                            };

  class _Cpo {
  private:
    enum class _St_all_opt { _None, _Non_member };
    enum class _St_all_evf_opt { _None, _Non_member };

    template <class G, class Alloc>
    [[nodiscard]] static consteval _Choice_t<_St_all_opt> _Choose_all_opt() noexcept {
      if constexpr (_Has_all<G>) {
        return {_St_all_opt::_Non_member, noexcept(_Fake_copy_init(sourced_edges_depth_first_search(
                                                declval<G>(), declval<vertex_id_t<G>>(), declval<Alloc>())))};
      } else {
        return {_St_all_opt::_None};
      }
    }
    template <class G, class Alloc>
    static constexpr _Choice_t<_St_all_opt> _Choice_all = _Choose_all_opt<G, Alloc>();

    template <class G, class EVF, class Alloc>
    [[nodiscard]] static consteval _Choice_t<_St_all_evf_opt> _Choose_all_evf_opt() noexcept {
      if constexpr (_Has_all_evf<G>) {
        return {_St_all_evf_opt::_Non_member,
                noexcept(_Fake_copy_init(sourced_edges_depth_first_search(
                      std::declval<G>(), declval<vertex_id_t<G>>(), std::declval<EVF>(), std::declval<Alloc>())))};
      } else {
        return {_St_all_evf_opt::_None};
      }
    }
    template <class G, class EVF, class Alloc>
    static constexpr _Choice_t<_St_all_evf_opt> _Choice_all_evf = _Choose_all_evf_opt<G, EVF, Alloc>();

  public:
    /**
     * @brief Get edges of a seed vertex recursively in depth-first order.
     *        Edges returned include the source and target vertices.
     * 
     * Complexity: O(N)
     * 
     * Default implementation: sourced_edges_depth_first_search_view<G, void, true, Stack>(g, seed, alloc);
     * 
     * @tparam G     The graph type.
     * @tparam Stack Stack type (used internally)
     * @tparam Alloc Allocator type
     * 
     * @param g     A graph instance.
     * @param seed  Vertex id to get the outgoing edges for.
     * @param alloc Allocator used for internal storage
     * 
     * @return The range of depth-first edges on a vertex with value_type of edge_descriptor<vertex_id_t<G>, true, edge_reference_t<G>>.
    */
    template <adjacency_list G, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
    requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> &&
             _detail::is_allocator_v<Alloc>
    [[nodiscard]] constexpr auto operator()(G&& g, vertex_id_t<G>&& seed, const Alloc& alloc = Alloc()) const
          noexcept(_Choice_all<G, Alloc>._No_throw) {
      if constexpr (_Choice_all<G, Alloc>()._Strategy == _St_all_opt::_Non_member) {
        return sourced_edges_depth_first_search(forward<decltype(g)>(g),       //
                                                forward<decltype(seed)>(seed), //
                                                alloc);
      } else {
        return edges_depth_first_search_view<G, void, true, Stack>(forward<decltype(g)>(g),       //
                                                                   forward<decltype(seed)>(seed), //
                                                                   alloc);
      }
    }

    /**
     * @brief Get edges of a seed vertex recursively with projected values, in depth-first order. 
     *        Edges returned include the source and target vertices.
     * 
     * Complexity: O(N)
     * 
     * Default implementation: sourced_edges_depth_first_search_view<G, EVF, true, Stack>(g, seed, evf, alloc);
     * 
     * @tparam G     The graph type.
     * @tparam EVF   Edge Value Function
     * @tparam Stack Stack type (used internally)
     * @tparam Alloc Allocator type
     * 
     * @param g      A graph instance.
     * @param seed   Vertex id to get the outgoing edges for.
     * @param evf    Function that takes an edge reference and returns an edge value.
     * @param alloc  Allocator used for internal storage
     * 
     * @return The range of depth-first edges of a vertex with value_type of edge_descriptor<vertex_id_t<G>, true, edge_reference<G>, decltype(evf())>.
    */
    template <adjacency_list G, class EVF, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
    requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> &&
             invocable<EVF, edge_reference_t<G>> && _detail::is_allocator_v<Alloc>
    [[nodiscard]] constexpr auto operator()(G&& g, vertex_id_t<G>&& seed, EVF&& evf, const Alloc& alloc = Alloc()) const
          noexcept(_Choice_all_evf<G, EVF, Alloc>._No_throw) {
      if constexpr (_Choice_all_evf<G, EVF, Alloc>()._Strategy == _St_all_opt::_Non_member) {
        return sourced_edges_depth_first_search(forward<decltype(g)>(g),       //
                                                forward<decltype(seed)>(seed), //
                                                forward<decltype(evf)>(evf),   //
                                                alloc);
      } else {
        return edges_depth_first_search_view<G, EVF, true, Stack>(forward<decltype(g)>(g),       //
                                                                  forward<decltype(seed)>(seed), //
                                                                  forward<decltype(evf)>(evf),   //
                                                                  alloc);
      }
    }
  };

} // namespace _Sourced_edges_depth_first_search

inline namespace _Cpos {
  inline constexpr _Sourced_edges_depth_first_search::_Cpo sourced_edges_depth_first_search;
}


#  else
namespace std::graph::tag_invoke {
// vertices_depth_first_search CPO
TAG_INVOKE_DEF(vertices_depth_first_search); // vertices_depth_first_search(g,seed)    -> vertices[vid,v]
                                             // vertices_depth_first_search(g,seed,fn) -> vertices[vid,v,value]

template <class G, class A>
concept _has_vtx_dfs_adl = vertex_range<G> && requires(G&& g, vertex_id_t<G> seed, const A& alloc) {
  { vertices_depth_first_search(g, seed, alloc) };
};
template <class G, class VVF, class A>
concept _has_vtx_dfs_vvf_adl = vertex_range<G> && requires(G&& g, vertex_id_t<G> seed, const VVF& vvf, const A& alloc) {
  { vertices_depth_first_search(g, seed, vvf, alloc) };
};

// edges_depth_first_search CPO
//  sourced_edges_depth_first_search
TAG_INVOKE_DEF(edges_depth_first_search);         // edges_depth_first_search(g,seed)    -> edges[vid,v]
                                                  // edges_depth_first_search(g,seed,fn) -> edges[vid,v,value]
TAG_INVOKE_DEF(sourced_edges_depth_first_search); // sourced_edges_depth_first_search(g,seed)    -> edges[uid,vid,v]
      // sourced_edges_depth_first_search(g,seed,fn) -> edges[uid,vid,v,value]

template <class G, class A>
concept _has_edg_dfs_adl = vertex_range<G> && requires(G&& g, vertex_id_t<G> seed, const A& alloc) {
  { edges_depth_first_search(g, seed, alloc) };
};
template <class G, class EVF, class A>
concept _has_edg_dfs_evf_adl = vertex_range<G> && requires(G&& g, vertex_id_t<G> seed, const EVF& evf, const A& alloc) {
  { edges_depth_first_search(g, seed, evf, alloc) };
};

template <class G, class A>
concept _has_src_edg_dfs_adl = vertex_range<G> && requires(G&& g, vertex_id_t<G> seed, const A& alloc) {
  { sourced_edges_depth_first_search(g, seed, alloc) };
};
template <class G, class EVF, class A>
concept _has_src_edg_dfs_evf_adl =
      vertex_range<G> && requires(G&& g, vertex_id_t<G> seed, const EVF& evf, const A& alloc) {
        { sourced_edges_depth_first_search(g, seed, evf, alloc) };
      };
} // namespace std::graph::tag_invoke


namespace std::graph::views {

//
// vertices_depth_first_search(g,uid,alloc)
// vertices_depth_first_search(g,uid,vvf,alloc)
//
template <adjacency_list G, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> && _detail::is_allocator_v<Alloc>
constexpr auto vertices_depth_first_search(G&& g, vertex_id_t<G> seed, const Alloc& alloc = Alloc()) {
  if constexpr (std::graph::tag_invoke::_has_vtx_dfs_adl<G, Alloc>)
    return std::graph::tag_invoke::vertices_depth_first_search(g, seed, alloc);
  else
    return vertices_depth_first_search_view<G, void, Stack>(g, seed, alloc);
}

template <adjacency_list G, class VVF, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> &&
         invocable<VVF, vertex_reference_t<G>> && _detail::is_allocator_v<Alloc>
constexpr auto vertices_depth_first_search(G&& g, vertex_id_t<G> seed, const VVF& vvf, const Alloc& alloc = Alloc()) {
  if constexpr (std::graph::tag_invoke::_has_vtx_dfs_vvf_adl<G, VVF, Alloc>)
    return std::graph::tag_invoke::vertices_depth_first_search(g, seed, vvf, alloc);
  else
    return vertices_depth_first_search_view<G, VVF, Stack>(g, seed, vvf, alloc);
}

//
// edges_depth_first_search(g,uid,alloc)
// edges_depth_first_search(g,uid,evf,alloc)
//
template <adjacency_list G, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> && _detail::is_allocator_v<Alloc>
constexpr auto edges_depth_first_search(G&& g, vertex_id_t<G> seed, const Alloc& alloc = Alloc()) {
  if constexpr (std::graph::tag_invoke::_has_edg_dfs_adl<G, Alloc>)
    return std::graph::tag_invoke::edges_depth_first_search(g, seed, alloc);
  else
    return edges_depth_first_search_view<G, void, false, Stack>(g, seed, alloc);
}

template <adjacency_list G, class EVF, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> &&
         invocable<EVF, edge_reference_t<G>> && _detail::is_allocator_v<Alloc>
constexpr auto edges_depth_first_search(G&& g, vertex_id_t<G> seed, const EVF& evf, const Alloc& alloc = Alloc()) {
  if constexpr (std::graph::tag_invoke::_has_edg_dfs_evf_adl<G, EVF, Alloc>)
    return std::graph::tag_invoke::edges_depth_first_search(g, seed, evf, alloc);
  else
    return edges_depth_first_search_view<G, EVF, false, Stack>(g, seed, evf, alloc);
}

//
// sourced_edges_depth_first_search(g,uid,alloc)
// sourced_edges_depth_first_search(g,uid,evf,alloc)
//
template <adjacency_list G, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> && _detail::is_allocator_v<Alloc>
constexpr auto sourced_edges_depth_first_search(G&& g, vertex_id_t<G> seed, const Alloc& alloc = Alloc()) {
  if constexpr (std::graph::tag_invoke::_has_src_edg_dfs_adl<G, Alloc>)
    return std::graph::tag_invoke::sourced_edges_depth_first_search(g, seed, alloc);
  else
    return edges_depth_first_search_view<G, void, true, Stack>(g, seed, alloc);
}

template <adjacency_list G, class EVF, class Stack = stack<dfs_element<G>>, class Alloc = allocator<bool>>
requires ranges::random_access_range<vertex_range_t<G>> && integral<vertex_id_t<G>> &&
         invocable<EVF, edge_reference_t<G>> && _detail::is_allocator_v<Alloc>
constexpr auto
sourced_edges_depth_first_search(G&& g, vertex_id_t<G> seed, const EVF& evf, const Alloc& alloc = Alloc()) {
  if constexpr (std::graph::tag_invoke::_has_src_edg_dfs_evf_adl<G, EVF, Alloc>)
    return std::graph::tag_invoke::sourced_edges_depth_first_search(g, seed, evf, alloc);
  else
    return edges_depth_first_search_view<G, EVF, true, Stack>(g, seed, evf, alloc);
}


} // namespace std::graph::views

#  endif //NEW_CPO

#endif   // GRAPH_DFS_HPP
