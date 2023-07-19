#pragma once

/**
 * @defgroup general_concepts   Concepts
 * 
 * @defgroup graph_algorithms   Algorithms
 * @defgroup graph_views        Views / Adaptors
 * @defgroup graph_containers   Containers
 * @defgroup graph_construction Graph Construction
 * @defgroup graph_io           Graph I/O
 * @defgroup graph_utilities    Utilities
 * 
 * @defgroup graph_concepts Graph Concepts
 * @ingroup general_concepts
 * 
 * @defgroup graph_properties Graph Property Concepts
 * @ingroup general_concepts
 */

#include <ranges>
#include <concepts>
#include <type_traits>

#define NEW_CPO

#ifdef NEW_CPO
#include "detail/graph_cpo2.hpp"
#else
#include "detail/graph_cpo.hpp"
#endif

// Naming Conventions
//
// Template
// Parameter Variables      Description
// --------- -------------- ----------------------------------------------------
// G         g              Graph
// GV                       Graph Value (user-defined or void)
//
// V                        Vertex type
//           u,v,x,y        Vertex reference
// VId       uid,vid,seed   Vertex Id
// VV                       Vertex Value (user-defined or void)
// VR                       Vertex Range
// VI        ui,vi          Vertex Iterator
// VVF                      Vertex Value Function: vvf(u) -> value
//
// E                        Edge type
//           uv,vw          Edge reference
// EV                       Edge Value (user-defined or void)
// ER                       Edge Range
// EI        uvi,vwi        Edge iterator
// EVF       evf            Edge Value Function: evf(uv) -> value
//

#ifndef GRAPH_HPP
#  define GRAPH_HPP

namespace std::graph {
/**
 * @ingroup graph_properties
 * @brief Override for an edge type where source and target are unordered
 * 
 * For instance, given:
 *  @code
 *      vertex_iterator_t<G> ui = ...;
 *      for(auto&& uv : edges(g,*ui)) ...
 *  @endcode
 *  if(source_id(g,u) != vertex_id(ui)) then target_id(g,u) == vertex_id(ui)
 *
 * Example:
 *  @code
 *  namespace my_namespace {
 *      template<class X>
 *      class my_graph { ... };
 *  }
 *  namespace std::graph {
 *     template<class X>
 *     inline constexpr bool is_undirected_edge_v<edge_t<my_namespace::my_graph<X>>> = true;
 *  }
 *  @endcode
 * 
 * @tparam name E The edge type with unordered source and target
 */
template <class E>
inline constexpr bool is_undirected_edge_v = false;

//
// graph concepts
//


/**
 * @ingroup graph_concepts
 * @brief Concept for a range of vertices.
 * 
 * A vertex range must be a sized forward range, at a minimum.
 *
 * Required functions that must also be defined include
 *  * @c vertices(g) that returns a range of vertices of a graph.
 *  * @c vertex_id(g,ui) that returns a vertex id for a graph and vertex iterator of the graph.
 * 
 * @tparam G The graph type.
 */
template <class G>
concept vertex_range = ranges::forward_range<vertex_range_t<G>> && ranges::sized_range<vertex_range_t<G>> &&
                       requires(G&& g, vertex_iterator_t<G> ui) {
                         { vertices(g) } -> ranges::forward_range;
                         vertex_id(g, ui);
                       };

/**
 * @ingroup graph_concepts
 * @brief Concept for a targeted edge.
 * 
 * A targeted edge has both @c target_id(g,uv) and @c target(g,uv) functions defined for it.
 * 
 * @tparam G The graph type.
 * @tparam E The edge type.
 */
template <class G, class E>
concept targeted_edge = requires(G&& g, edge_reference_t<G> uv) {
  target_id(g, uv);
  target(g, uv);
};

/**
 * @ingroup graph_concepts
 * @brief Concept for a sourced edge.
 * 
 * A sourced edge has both @c source_id(g,uv) and @c source(g,uv) functions defined for it.
 * 
 * @tparam G The graph type.
 * @tparam E The edge type.
 */
template <class G, class E>
concept sourced_edge = requires(G&& g, E& uv) {
  source_id(g, uv);
  source(g, uv);
};

/**
 * @brief Type trait to determine if an edge is sourced.
 * 
 * Use @c is_sourced_edge<G,E>::value to deterine if the edge is sourced.
 * 
 * @tparam G The graph type.
 * @tparam E The edge type.
*/
template <class G, class E>
struct is_sourced_edge : public integral_constant<bool, sourced_edge<G, E>> {};

/**
 * @brief Type trait helper to determine if an edge is sourced.
 * 
 * Use @c is_sourced_edge_v<G,E> to deterine if the edge is sourced.
 * 
 * @tparam G The graph type.
 * @tparam E The edge type.
*/
template <class G, class E>
inline constexpr bool is_sourced_edge_v = is_sourced_edge<G, E>::value;

/**
 * @ingroup graph_concepts
 * @brief Concept for an adjacency list graph.
 * 
 * An adjacency list requires that the vertices range is a forward range, it has a targeted edge,
 * and functions edges(g,u) and edges(g,uid) are defined.
 * 
 * @tparam G The graph type.
*/
template <class G>
concept adjacency_list =
      vertex_range<G> && targeted_edge<G, edge_t<G>> && requires(G&& g, vertex_reference_t<G> u, vertex_id_t<G> uid) {
        { edges(g, u) } -> ranges::forward_range;
        { edges(g, uid) } -> ranges::forward_range;
      };
// !is_same_v<vertex_range_t<G>, vertex_edge_range_t<G>>
//      CSR fails this condition b/c row_index & col_index are both index_vectors; common?

/**
 * @ingroup graph_concepts
 * @brief Concept for a sourced adjacency list.
 * 
 * A sourced adjacency list extends the adjacency list by requiring that edges are souced edges
 * and edge_id(g,uv) is defined.
 * 
 * @tparam G The graph type.
*/
template <class G>
concept sourced_adjacency_list =
      adjacency_list<G> && sourced_edge<G, edge_t<G>> && requires(G&& g, edge_reference_t<G> uv) { edge_id(g, uv); };

//
// property concepts
//

/**
 * @ingroup graph_properties
 * @brief Concept for the existance of degree function for graph G.
 * 
 * Returns true if degree(g) exists for graph G.
 * 
 * @tparam G The graph type
*/
template <class G>
concept has_degree = requires(G&& g, vertex_reference_t<G> u) {
  { degree(g, u) };
};

//
// find/contains concepts
//

/**
 * @ingroup graph_properties
 * @brief Concept for the existance of the find_vertex(g,uid) function for graph G.
 * 
 * Returns true if find_vertex(g,uid) exists for graph G.
 * 
 * @tparam G The graph type
*/
template <class G>
concept has_find_vertex = requires(G&& g, vertex_id_t<G> uid) {
  { find_vertex(g, uid) } -> forward_iterator;
};

/**
 * @ingroup graph_properties
 * @brief Concept for the existance of the find_vertex_edge(g,uid,vid) function for graph G.
 * 
 * Returns true if find_vertex_edge(g,u,vid) and find_vertex_edge(g,uid,vid) exists for graph G.
 * 
 * @tparam G The graph type
*/
template <class G>
concept has_find_vertex_edge = requires(G&& g, vertex_id_t<G> uid, vertex_id_t<G> vid, vertex_reference_t<G> u) {
  { find_vertex_edge(g, u, vid) } -> forward_iterator;
  { find_vertex_edge(g, uid, vid) } -> forward_iterator;
};

/**
 * @ingroup graph_properties
 * @brief Concept for the existance of the has_contains_edge(g,uid,vid) function for graph G.
 * 
 * Returns true if has_contains_edge(g,uid,vid) exists for graph G.
 * 
 * @tparam G The graph type
*/
template <class G>
concept has_contains_edge = requires(G&& g, vertex_id_t<G> uid, vertex_id_t<G> vid) {
  { contains_edge(g, uid, vid) } -> convertible_to<bool>;
};


/**
 * @ingroup graph_properties
 * @ brief Specializable to define that a graph type has unordered edges.
 * 
 * Override for a graph type where source_id and target_id are unordered
 * on an edge so views and algorithms know to choose the correct target
 * based on where they came from.
 *
 * An unordered edge implies sourced_edge<G> is true so that an algorithm can
 * decide if source_id(g,uv) or target_id(g,uv) is the true target, based on
 * where the algorithm came from.
 *
 * If a graph container implementation has a run-time property of ordered or
 * unordered (e.g. it can't be determined at compile-time) then unordered_edge<G,E>
 * should be true_type. The only consequence is that an additional if is done to
 * check whether source_id or target_id is used for the target in this library.
 * The container implementation can still preserve its implementation of order,
 * assuming it always includes a source_id on the edge.
 *
 * Example:
 *  namespace my_namespace {
 *      template <class T>
 *      class my_graph { ... };
 *      template class< T>
 *      class my_edge { int src_id; int tgt_id; ... };
 *  }
 *  namespace std::graph {
 *     template<class T>
 *     struct define_unordered_edge<my_namespace::my_graph<T>, my_namespace::my_edge<T>> : public true_type {};
 *  }
 *
 * @tparam G Graph type
 */

template <class E>
struct define_unordered_edge : public false_type {}; // specialized for graph container edge

template <class G, class E>
struct is_unordered_edge : public conjunction<define_unordered_edge<E>, is_sourced_edge<G, E>> {};

template <class G, class E>
inline constexpr bool is_unordered_edge_v = is_unordered_edge<G, E>::value;

template <class G, class E>
concept unordered_edge = is_unordered_edge_v<G, E>;

//
// is_ordered_edge, ordered_edge
//
template <class G, class E>
struct is_ordered_edge : public negation<is_unordered_edge<G, E>> {};

template <class G, class E>
inline constexpr bool is_ordered_edge_v = is_ordered_edge<G, E>::value;

template <class G, class E>
concept ordered_edge = is_ordered_edge_v<G, E>;


} // namespace std::graph

#endif //GRAPH_HPP
