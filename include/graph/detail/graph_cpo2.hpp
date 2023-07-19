#pragma once

// hand-crafted Customization Point Objects (CPO)
//	reference std::ranges::size(r)
//		MSVC xutility:       namespace _Size,
//		gcc11 ranges_base.h: struct _Size (in __cust_access), namespace __cust
//
// Microsoft style chosen for clarity.
//
// NOTES
//  added degree(g,u) (in addition to degree(g,uid))
//  use of const& for vertex_id_t<G>
//
//  use member impl over free fnc impl when present? (current impl)
//  should both member & free fnc API be supported?
//

namespace std::graph {

#ifndef _MSC_VER
// Taken from gcc11 definition of __decay_copy().
// Very similar (identical?) to std::_Fake_copy_init<T> in msvc.
struct _Decay_copy final {
  template <typename _Tp>
  constexpr decay_t<_Tp> operator()(_Tp&& __t) const noexcept(is_nothrow_convertible_v<_Tp, decay_t<_Tp>>) {
    return std::forward<_Tp>(__t);
  }
} inline constexpr _Fake_copy_init{};

template <class _Ty>
concept _Has_class_or_enum_type = __is_class(remove_reference_t<_Ty>) || __is_enum(remove_reference_t<_Ty>) ||
                                  __is_union(remove_reference_t<_Ty>);

template <class>
// false value attached to a dependent name (for static_assert)
inline constexpr bool _Always_false = false;

template <class _Ty>
inline constexpr bool _Is_nonbool_integral = is_integral_v<_Ty> && !is_same_v<remove_cv_t<_Ty>, bool>;

template <class _Ty>
inline constexpr bool _Integer_class = requires {
                                         typename _Ty::_Signed_type;
                                         typename _Ty::_Unsigned_type;
                                       };

template <class _Ty>
concept _Integer_like = _Is_nonbool_integral<remove_cv_t<_Ty>> || _Integer_class<_Ty>;

template <class _Ty>
concept _Signed_integer_like = _Integer_like<_Ty> && static_cast<_Ty>(-1) < static_cast<_Ty>(0);

template <class _Ty>
struct _Choice_t {
  _Ty  _Strategy = _Ty{};
  bool _No_throw = false;
};
#endif

template <class G>
using graph_reference_t = add_lvalue_reference<G>;


/** 
 * @brief Tag a graph type as an adjacency matrix.
 * 
 * Specialize for a graph type where edges are defined densely in a matrix to allow for
 * optimized algorithms can take advantage of the memory layout.
 *
 * Example:
 * @code
 *  namespace my_namespace {
 *      template<class X>
 *      class my_graph { ... };
 *  }
 *  namespace std::graph {
 *     template<>
 *     struct is_adjacency_matrix<my_namespace::my_graph<X>> : true_type;
 *  }
 * @endcode
 * 
 * @tparam G The graph type
 */
template <class G>
struct define_adjacency_matrix : public false_type {}; // specialized for graph container

template <class G>
struct is_adjacency_matrix : public define_adjacency_matrix<G> {};

template <class G>
inline constexpr bool is_adjacency_matrix_v = is_adjacency_matrix<G>::value;

template <class G>
concept adjacency_matrix = is_adjacency_matrix_v<G>;

//
// vertices(g) -> vertex_range_t<G>
//
// vertex_range_t<G>     = decltype(vertices(g))
// vertex_iterator_t<G>  = ranges::iterator_t<vertex_range_t<G>>
// vertex_t<G>           = ranges::range_value_t<vertex_range_t<G>>
// vertex_reference_t<G> = ranges::range_reference_t<vertex_range_t<G>>
//
namespace _Vertices {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void vertices() = delete;                // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void vertices();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_member = requires(_G&& __g) {
                          { _Fake_copy_init(__g.vertices()) } -> ranges::range;
                        };

  template <class _G, class _UnCV>
  concept _Has_ADL = _Has_class_or_enum_type<_G> //
                     && requires(_G&& __g) {
                          { _Fake_copy_init(vertices(__g)) } -> ranges::range; // intentional ADL
                        };

  class _Cpo {
  private:
    enum class _St { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St> _Choose() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_member<_G, _UnCV>) {
        return {_St::_Member, noexcept(_Fake_copy_init(declval<_G>().vertices()))};
      } else if constexpr (_Has_ADL<_G, _UnCV>) {
        return {_St::_Non_member, noexcept(_Fake_copy_init(vertices(declval<_G>())))}; // intentional ADL
      } else {
        return {_St::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St> _Choice = _Choose<_G>();

  public:
    template <class _G>
    requires(_Choice<_G&>._Strategy != _St::_None)
    [[nodiscard]] constexpr auto operator()(_G&& _Val) const noexcept(_Choice<_G&>._No_throw) {
      constexpr _St _Strat = _Choice<_G&>._Strategy;

      if constexpr (_Strat == _St::_Member) {
        return _Val.vertices();
      } else if constexpr (_Strat == _St::_Non_member) {
        return vertices(_Val); // intentional ADL
      } else {
        static_assert(_Always_false<_G>, "vertices(g) is not defined");
      }
    }
  };
} // namespace _Vertices

inline namespace _Cpos {
  inline constexpr _Vertices::_Cpo vertices;
}

/**
 * @brief The vertex range type for a graph G.
 * @tparam G The graph type.
 */
template <class G>
using vertex_range_t = decltype(std::graph::vertices(declval<G&&>()));

/**
 * @brief The vertex iterator type for a graph G.
 * @tparam G The graph type.
 */
template <class G>
using vertex_iterator_t = ranges::iterator_t<vertex_range_t<G&&>>;

/**
 * @brief The vertex type for a graph G.
 * @tparam G The graph type.
 */
template <class G>
using vertex_t = ranges::range_value_t<vertex_range_t<G>>;

/**
 * @brief The vertex reference type for a graph G.
 * @tparam G The graph type.
*/
template <class G>
using vertex_reference_t = ranges::range_reference_t<vertex_range_t<G>>;


//
// vertex_id(g,ui) -> vertex_id_t<_G>
//      default = ui - begin(vertices(g)), if random_access_iterator<ui>
//
namespace _Vertex_id {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void vertex_id() = delete;               // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void vertex_id();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_member = requires(_G&& __g, vertex_iterator_t<_G> ui) {
                          { _Fake_copy_init(__g.vertex_id(ui)) };
                        };

  template <class _G, class _UnCV>
  concept _Has_ADL = _Has_class_or_enum_type<_G> //
                     && requires(_G&& __g, vertex_iterator_t<_G> ui) {
                          { _Fake_copy_init(vertex_id(__g, ui)) }; // intentional ADL
                        };

  class _Cpo {
  private:
    enum class _St { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St> _Choose() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_member<_G, _UnCV>) {
        return {_St::_Member, noexcept(_Fake_copy_init(declval<_G>().vertex_id(declval<vertex_iterator_t<_G>>())))};
      } else if constexpr (_Has_ADL<_G, _UnCV>) {
        return {
              _St::_Non_member,
              noexcept(_Fake_copy_init(vertex_id(declval<_G>(), declval<vertex_iterator_t<_G>>())))}; // intentional ADL
      } else {
        return {_St::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St> _Choice = _Choose<_G>();

  public:
    /**
     * @brief Get's the id of a vertex.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: ui - begin(g), when vertex_iterator_t<_G> is random_access
     * 
     * This is a customization point function that may be overriden for a graph type.
     * The main reason to do so is to change the return type to be something different
     * than range_difference_t<vertex_range_t<_G>>. For 64-bit systems, that's typically
     * int64_t. The return type is used to define the type vertex_id_t<_G> which is used
     * for vertex id in other functions.
     * 
     * Why does this function take a vertex iterator instead of a vertex reference?
     * The vertex id is often calculated rather than stored. Given an iterator, the id is easily
     * calculated by id = (ui - begin(vertices(g))). If a vertex reference v is passed instead
     * it is also easily calculated for vertices stored in contiguous memory like std::vector.
     * However, if it's a random access container like a deque, then the reference won't work
     * and an iterator is the only option.
     * 
     * @tparam _G The graph type.
     * @param g A graph instance.
     * @param ui A vertex iterator for a vertext in graph _G.
     * @return The vertex id of a vertex.
    */
    template <class _G>
    requires(_Choice<_G&>._Strategy != _St::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, vertex_iterator_t<_G> ui) const noexcept(_Choice<_G&>._No_throw) {
      constexpr _St _Strat = _Choice<_G&>._Strategy;

      if constexpr (_Strat == _St::_Member) {
        return __g.vertex_id(ui);
      } else if constexpr (_Strat == _St::_Non_member) {
        return vertex_id(__g, ui); // intentional ADL
      } else if constexpr (random_access_iterator<vertex_iterator_t<_G>>) {
        return ui - ranges::begin(vertices(__g)); // default impl for random_access_iterator
      } else {
        static_assert(_Always_false<_G>,
                      "vertex_id(g,u) is not defined and the default implemenation cannot be evaluated");
      }
    }
  };
} // namespace _Vertex_id

inline namespace _Cpos {
  inline constexpr _Vertex_id::_Cpo vertex_id;
}

/**
 * @brief Defines the type of the vertex id.
 * 
 * Complexity: O(1)
 * 
 * The vertex id type for graph type G.
 * 
 * @tparam G The graph type.
*/
template <class _G>
using vertex_id_t = decltype(vertex_id(declval<_G&&>(), declval<vertex_iterator_t<_G>>()));


//
// find_vertex(g,uid) -> vertex_iterator_t<G>
//
// default = begin(vertices(g)) + uid, if random_access_range<vertex_range_t<G>>
//
namespace _Find_vertex {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void find_vertex() = delete;             // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void find_vertex();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_member = requires(_G&& __g, const vertex_id_t<_G>& uid) {
                          { _Fake_copy_init(__g.find_vertex(uid)) };
                        };

  template <class _G, class _UnCV>
  concept _Has_ADL = _Has_class_or_enum_type<_G> //
                     && requires(_G&& __g, const vertex_id_t<_G>& uid) {
                          { _Fake_copy_init(find_vertex(__g, uid)) }; // intentional ADL
                        };

  class _Cpo {
  private:
    enum class _St { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St> _Choose() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_member<_G, _UnCV>) {
        return {_St::_Member, noexcept(_Fake_copy_init(declval<_G>().find_vertex(declval<vertex_id_t<_G>>())))};
      } else if constexpr (_Has_ADL<_G, _UnCV>) {
        return {_St::_Non_member,
                noexcept(_Fake_copy_init(find_vertex(declval<_G>(), declval<vertex_id_t<_G>>())))}; // intentional ADL
      } else {
        return {_St::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St> _Choice = _Choose<_G>();

  public:
    /**
     * @brief Find a vertex given a vertex id.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: begin(vertices(g)) + uid, if random_access_range<vertex_range_t<G>>
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uid Vertex id.
     * @return An iterator to the vertex if the vertex exists, or end(vertices(g)) if it doesn't exist.
    */
    template <class _G>
    requires(_Choice<_G&>._Strategy != _St::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, const vertex_id_t<_G>& uid) const
          noexcept(_Choice<_G&>._No_throw) {
      constexpr _St _Strat = _Choice<_G&>._Strategy;

      if constexpr (_Strat == _St::_Member) {
        return __g.find_vertex(uid);
      } else if constexpr (_Strat == _St::_Non_member) {
        return find_vertex(__g, uid); // intentional ADL
      } else if constexpr (random_access_iterator<vertex_iterator_t<_G>>) {
        auto uid_diff = static_cast<ranges::range_difference_t<vertex_range_t<_G>>>(uid);
        if (uid_diff < size(vertices(__g)))
          return begin(vertices(__g)) + uid_diff;
        else
          return end(vertices(__g));
      } else {
        static_assert(_Always_false<_G>,
                      "find_vertex(g,uid) has not been defined and the default implemenation cannot be evaluated");
      }
    }
  };
} // namespace _Find_vertex

inline namespace _Cpos {
  inline constexpr _Find_vertex::_Cpo find_vertex;
}


//
// edges(g,u)  -> vertex_edge_range_t<G>
// edges(g,uid) -> vertex_edge_range_t<G>
//      default = edges(g,*find_vertex(g,uid))
//
// vertex_edge_range_t<G>    = edges(g,u)
// vertex_edge_iterator_t<G> = ranges::iterator_t<vertex_edge_range_t<G>>
// edge_t                    = ranges::range_value_t<vertex_edge_range_t<G>>
// edge_reference_t          = ranges::range_reference_t<vertex_edge_range_t<G>>
//
namespace _Edges {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void edges() = delete;                   // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void edges();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, vertex_reference_t<_G> u) {
                              { _Fake_copy_init(u.edges(__g)) };
                            };
  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const vertex_reference_t<_G>& u) {
                              { _Fake_copy_init(edges(__g, u)) }; // intentional ADL
                            };

  template <class _G, class _UnCV>
  concept _Has_id_ADL = _Has_class_or_enum_type<_G> //
                        && requires(_G&& __g, const vertex_id_t<_G>& uid) {
                             { _Fake_copy_init(edges(__g, uid)) }; // intentional ADL
                           };

  template <class _G, class _UnCV>
  concept _Can_id_eval = _Has_class_or_enum_type<_G>                                //
                         && (_Has_ref_member<_G, _UnCV> || _Has_ref_ADL<_G, _UnCV>) // u.edges(g) || edges(g,u)
                         && requires(_G&& __g, const vertex_id_t<_G>& uid) {
                              { _Fake_copy_init(find_vertex(__g, uid)) };
                            };


  class _Cpo {
  private:
    enum class _St_id { _None, _Non_member, _Auto_eval };
    enum class _St_ref { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<vertex_reference_t<_G>>().edges(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {_St_ref::_Non_member,
                noexcept(_Fake_copy_init(edges(declval<_G>(), declval<vertex_reference_t<_G>>())))}; // intentional ADL
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_id> _Choose_id() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_id_ADL<_G, _UnCV>) {
        return {_St_id::_Non_member,
                noexcept(_Fake_copy_init(edges(declval<_G>(), declval<vertex_id_t<_G>>())))}; // intentional ADL
      } else if constexpr (_Can_id_eval<_G, _UnCV>) {
        return {_St_id::_Auto_eval,
                noexcept(_Fake_copy_init(edges(
                      declval<_G>(), *find_vertex(declval<_G>(), declval<vertex_id_t<_G>>()))))}; // intentional ADL
      } else {
        return {_St_id::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_id> _Choice_id = _Choose_id<_G>();

  public:
    /**
     * @brief Get the outgoing edges of a vertex.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: n/a. This must be specialized for each graph type.
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param u Vertex reference.
     * @return A range of the outgoing edges.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, vertex_reference_t<_G> u) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_ref = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_ref == _St_ref::_Member) {
        return __g.edges(u);
      } else if constexpr (_Strat_ref == _St_ref::_Non_member) {
        return edges(__g, u); // intentional ADL
      } else {
        static_assert(_Always_false<_G>, "edges(g,u) is not defined");
      }
    }

    /**
     * @brief Get the outgoing edges of a vertex id.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: edges(g, *find_vertex(g, uid))
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uid Vertex id.
     * @return A range of the outgoing edges.
    */
    template <class _G>
    requires(_Choice_id<_G&>._Strategy != _St_id::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, const vertex_id_t<_G>& uid) const
          noexcept(_Choice_id<_G&>._No_throw) {
      constexpr _St_id _Strat_id = _Choice_id<_G&>._Strategy;

      if constexpr (_Strat_id == _St_id::_Non_member) {
        return edges(__g, uid); // intentional ADL
      } else if constexpr (_Strat_id == _St_id::_Auto_eval) {
        return (*this)(__g, *find_vertex(__g, uid)); // default impl
      } else {
        static_assert(_Always_false<_G>, "edges(g,uid) is not defined and default implementation cannot be evaluated");
      }
    }
  };
} // namespace _Edges

inline namespace _Cpos {
  inline constexpr _Edges::_Cpo edges;
}

/**
 * @brief The outgoing edge range type of a vertex for graph G.
 * @tparam G The graph type.
*/
template <class G>
using vertex_edge_range_t = decltype(edges(declval<G&&>(), declval<vertex_reference_t<G>>()));

/**
 * @brief The outgoing edge iterator type of a vertex for graph G.
 * @tparam G The graph type.
*/
template <class G>
using vertex_edge_iterator_t = ranges::iterator_t<vertex_edge_range_t<G>>;

/**
 * @brief The edge type for graph G.
 * @tparam G The graph type.
*/
template <class G>
using edge_t = ranges::range_value_t<vertex_edge_range_t<G>>;

/**
 * @brief The edge reference type for graph G.
 * @tparam G The graph type.
*/
template <class G>
using edge_reference_t = ranges::range_reference_t<vertex_edge_range_t<G>>;


//
// target_id(g,uv) -> vertex_id_t<G>
//
namespace _Target_id {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void target_id() = delete;               // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void target_id();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, edge_reference_t<_G> uv) {
                              { _Fake_copy_init(uv.target_id(__g)) };
                            };

  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const edge_reference_t<_G>& uv) {
                              { _Fake_copy_init(target_id(__g, uv)) }; // intentional ADL
                            };

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<edge_reference_t<_G>>().target_id(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {
              _St_ref::_Non_member,
              noexcept(_Fake_copy_init(target_id(declval<_G>(), declval<edge_reference_t<_G>>())))}; // intentional ADL
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief Get the target vertex id of an edge.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: n/a. This must be specialized for each graph type.
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uv An edge reference.
     * @return The target vertex id.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, edge_reference_t<_G> uv) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_ref = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_ref == _St_ref::_Member) {
        return uv.target_id(__g);
      } else if constexpr (_Strat_ref == _St_ref::_Non_member) {
        return target_id(__g, uv); // intentional ADL
      } else {
        static_assert(_Always_false<_G>, "target_id(g,uv) is not defined");
      }
    }
  };

} // namespace _Target_id

inline namespace _Cpos {
  inline constexpr _Target_id::_Cpo target_id;
}


//
// target(g,uv) -> vertex_reference_t<G>
//
namespace _Target {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void target() = delete;                  // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void target();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, edge_reference_t<_G> uv) {
                              { _Fake_copy_init(uv.target(__g)) };
                            };

  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const edge_reference_t<_G>& uv) {
                              { _Fake_copy_init(target(__g, uv)) }; // intentional ADL
                            };

  template <class _G, class _UnCV>
  concept _Can_eval = _Has_class_or_enum_type<_G> //
                      && ranges::random_access_range<vertex_range_t<_G>>;

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member, _Auto_eval };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<edge_reference_t<_G>>().target(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {_St_ref::_Non_member,
                noexcept(_Fake_copy_init(target(declval<_G>(), declval<edge_reference_t<_G>>())))}; // intentional ADL
      }
      if constexpr (_Can_eval<_G, _UnCV>) {
        return {_St_ref::_Auto_eval,
                noexcept(_Fake_copy_init(vertices(declval<_G>())))}; // Default impl; use vertices(g) to define noexcept
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief Get the target vertex of an edge.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: *(begin(vertices(g)) + target_id(g, uv))
     *                         if random_access_range<vertex_range_t<_G>>
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uv An edge reference.
     * @return The target vertex reference.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, edge_reference_t<_G> uv) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_ref = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_ref == _St_ref::_Member) {
        return uv.target(__g);
      } else if constexpr (_Strat_ref == _St_ref::_Non_member) {
        return target(__g, uv); // intentional ADL
      } else if constexpr (_Strat_ref == _St_ref::_Auto_eval) {
        return *(begin(vertices(__g)) + target_id(__g, uv)); // default impl
      } else {
        static_assert(_Always_false<_G>,
                      "target(g,uv) is not defined and the default implemenation cannot be evaluated");
      }
    }
  };

} // namespace _Target

inline namespace _Cpos {
  inline constexpr _Target::_Cpo target;
}


//
// source_id(g,uv) -> vertex_id_t<G>
//
namespace _Source_id {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void source_id() = delete;               // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void source_id();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, edge_reference_t<_G> uv) {
                              { _Fake_copy_init(uv.source_id(__g)) };
                            };

  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const edge_reference_t<_G>& uv) {
                              { _Fake_copy_init(source_id(__g, uv)) }; // intentional ADL
                            };

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<edge_reference_t<_G>>().source_id(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {
              _St_ref::_Non_member,
              noexcept(_Fake_copy_init(source_id(declval<_G>(), declval<edge_reference_t<_G>>())))}; // intentional ADL
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief Get the source vertex id of an edge.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: n/a. This must be specialized for each graph type.
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uv An edge reference.
     * @return The source vertex id.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, edge_reference_t<_G> uv) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_ref = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_ref == _St_ref::_Member) {
        return uv.source_id(__g);
      } else if constexpr (_Strat_ref == _St_ref::_Non_member) {
        return source_id(__g, uv); // intentional ADL
      } else {
        static_assert(_Always_false<_G>, "source_id(g,uv) is not defined");
      }
    }
  };

} // namespace _Source_id

inline namespace _Cpos {
  inline constexpr _Source_id::_Cpo source_id;
}


//
// source(g,uv) -> vertex_reference_t<G>
//      default = *(begin(g,vertices(g)) + source_id(g,uv))
//
//      for random_access_range<vertices(g)> and integral<source_id(g,uv))
//      uv can be from edges(g,u) or vertices(g,u)
//
namespace _Source {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void source() = delete;                  // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void source();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, edge_reference_t<_G> uv) {
                              { _Fake_copy_init(uv.source(__g)) };
                            };

  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const edge_reference_t<_G>& uv) {
                              { _Fake_copy_init(source(__g, uv)) }; // intentional ADL
                            };

  template <class _G, class _UnCV>
  concept _Can_eval = _Has_class_or_enum_type<_G> //
                      && ranges::random_access_range<vertex_range_t<_G>>;

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member, _Auto_eval };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<edge_reference_t<_G>>().source(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {_St_ref::_Non_member,
                noexcept(_Fake_copy_init(source(declval<_G>(), declval<edge_reference_t<_G>>())))}; // intentional ADL
      } else if constexpr (_Can_eval<_G, _UnCV>) {
        return {_St_ref::_Auto_eval,
                noexcept(_Fake_copy_init(vertices(declval<_G>())))}; // default; use vertices(g) to determine noexcept
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief Get the source vertex of an edge.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: *(begin(vertices(g)) + target_id(g, uv))
     *                         if random_access_range<vertex_range_t<_G>>
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uv An edge reference.
     * @return The source vertex reference.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, edge_reference_t<_G> uv) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_ref = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_ref == _St_ref::_Member) {
        return uv.source(__g);
      } else if constexpr (_Strat_ref == _St_ref::_Non_member) {
        return source(__g, uv); // intentional ADL
      } else if constexpr (_Strat_ref == _St_ref::_Auto_eval) {
        return *(begin(vertices(__g)) + target_id(__g, uv)); // default impl
      } else {
        static_assert(_Always_false<_G>,
                      "source(g,uv) is not defined and the default implemenation cannot be evaluated");
      }
    }
  };

} // namespace _Source

inline namespace _Cpos {
  inline constexpr _Source::_Cpo source;
}


//
// edge_id(g,uv) -> pair<vertex_id_t<G>,vertex_id_t<G>>
//      default = pair(source_id(g,uv),target_id(g,uv))
//
// edge_id_t<G> = decltype(edge_id(g,uv))
//
namespace _Edge_id {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void edge_id() = delete;                 // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void edge_id();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, edge_reference_t<_G> uv) {
                              { _Fake_copy_init(uv.edge_id(__g)) };
                            };

  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const edge_reference_t<_G>& uv) {
                              { _Fake_copy_init(edge_id(__g, uv)) }; // intentional ADL
                            };

  template <class _G, class _UnCV>
  concept _Can_eval = _Has_class_or_enum_type<_G> //
                      && requires(_G&& __g, const edge_reference_t<_G>& uv) {
                           { _Fake_copy_init(target_id(__g, uv)) };
                           { _Fake_copy_init(source_id(__g, uv)) };
                         };

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member, _Auto_eval };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<edge_reference_t<_G>>().edge_id(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {_St_ref::_Non_member,
                noexcept(_Fake_copy_init(edge_id(declval<_G>(), declval<edge_reference_t<_G>>())))}; // intentional ADL
      } else if constexpr (_Can_eval<_G, _UnCV>) {
        return {
              _St_ref::_Auto_eval,
              noexcept(_Fake_copy_init(target_id(declval<_G>(), declval<edge_reference_t<_G>>())))}; // intentional ADL
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief Get the edge id of an edge.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: pair(source_id(g, uv), target_id(g, uv))
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uv An edge reference.
     * @return The edge id as a pair of vertex id's.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, edge_reference_t<_G> uv) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_ref = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_ref == _St_ref::_Member) {
        return uv.edge_id(__g);
      } else if constexpr (_Strat_ref == _St_ref::_Non_member) {
        return edge_id(__g, uv); // intentional ADL
      } else if constexpr (_Strat_ref == _St_ref::_Auto_eval) {
        return pair(source_id(__g, uv), target_id(__g, uv)); // default impl
      } else {
        static_assert(_Always_false<_G>,
                      "edge_id(g,uv) is not defined and the default implemenation cannot be evaluated");
      }
    }
  };

} // namespace _Edge_id

inline namespace _Cpos {
  inline constexpr _Edge_id::_Cpo edge_id;
}


//
//
// find_vertex_edge(g,u,vid) -> vertex_edge_iterator<G>
//      default = find(edges(g,u), [](uv) {target_id(g,uv)==vid;}
//
// find_vertex_edge(g,uid,vid) -> vertex_edge_iterator<G>
//      default = find_vertex_edge(g,*find_vertex(g,uid),vid)
//
namespace _Find_vertex_edge {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void find_vertex_edge() = delete;        // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void find_vertex_edge();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, vertex_reference_t<_G> u, const vertex_id_t<_G>& vid) {
                              { _Fake_copy_init(u.find_vertex_edge(__g, vid)) };
                            };

  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, vertex_reference_t<_G> u, const vertex_id_t<_G>& vid) {
                              { _Fake_copy_init(find_vertex_edge(__g, u, vid)) }; // intentional ADL
                            };

  template <class _G, class _UnCV>
  concept _Can_eval_ref = _Has_class_or_enum_type<_G> //
                          && requires(_G&& __g, vertex_reference_t<_G> u, edge_reference_t<_G> uv) {
                               { _Fake_copy_init(edges(__g, u)) };
                               { _Fake_copy_init(target_id(__g, uv)) };
                             };

  //template <class _G, class _UnCV>
  //concept _Has_id_member = requires(_G&& __g, const vertex_id_t<_G>& uid, const vertex_id_t<_G>& vid) {
  //                           { _Fake_copy_init(uid.find_vertex_edge(__g, vid)) };
  //                         };

  template <class _G, class _UnCV>
  concept _Has_id_ADL = _Has_class_or_enum_type<_G> //
                        && requires(_G&& __g, const vertex_id_t<_G>& uid, const vertex_id_t<_G>& vid) {
                             { _Fake_copy_init(find_vertex_edge(__g, uid, vid)) }; // intentional ADL
                           };

  template <class _G, class _UnCV>
  concept _Can_eval_id = _Has_class_or_enum_type<_G> //
                         && (_Has_ref_member<_G, _UnCV> || _Has_ref_ADL<_G, _UnCV> ||
                             _Can_eval_ref<_G, _UnCV>) // requires find_vertex_edge(g,u,vid)
                         && requires(_G&& __g, vertex_id_t<_G> uid) {
                              { _Fake_copy_init(find_vertex(__g, uid)) };
                            };

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member, _Auto_eval };
    enum class _St_id { _None, _Non_member, _Auto_eval };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<vertex_reference_t<_G>>().find_vertex_edge(
                                        declval<_G>(), declval<vertex_id_t<_G>>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {_St_ref::_Non_member,
                noexcept(_Fake_copy_init(
                      find_vertex_edge(declval<_G>(), declval<vertex_reference_t<_G>>(), declval<vertex_id_t<_G>>())))};
      } else if constexpr (_Can_eval_ref<_G, _UnCV>) {
        return {_St_ref::_Auto_eval,
                noexcept(_Fake_copy_init(
                      edges(declval<_G>(),
                            declval<vertex_reference_t<_G>>())))}; // default impl; use edges(g,u) for noexept value
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_id> _Choose_id() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      //if constexpr (_Has_id_member<_G, _UnCV>) {
      //  return {_St_id::_Member, noexcept(_Fake_copy_init(declval<_G>().find_vertex_edge(declval<vertex_id_t<_G>>())))};
      //} else
      if constexpr (_Has_id_ADL<_G, _UnCV>) {
        return {_St_id::_Non_member,
                noexcept(_Fake_copy_init(find_vertex_edge(declval<_G>(), declval<vertex_id_t<_G>>(),
                                                          declval<vertex_id_t<_G>>())))}; // intentional ADL
      } else if constexpr (_Can_eval_id<_G, _UnCV>) {
        return {_St_id::_Auto_eval,
                noexcept(_Fake_copy_init(find_vertex(
                      declval<_G>(),
                      declval<vertex_id_t<_G>>())))}; // default eval; use find_vertex(g,uid) for noexcept value
      }

      else {
        return {_St_id::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();
    template <class _G>
    static constexpr _Choice_t<_St_id> _Choice_id = _Choose_id<_G>();

  public:
    /**
     * @brief Find an edge of a vertex.
     * 
     * Complexity: O(E), where |E| is the number of outgoing edges of vertex u
     * 
     * Default implementation: find_if(edges(g, u), [&g, &vid](auto&& uv) { return target_id(g, uv) == vid; })
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param u A vertex instance.
     * @param vid A target vertex id.
     * @return An edge iterator of an outgoing edge of u with a target id of vid. end(edges(g,u)) will
     *         be returned if an edge doesn't exist.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, vertex_reference_t<_G> u, const vertex_id_t<_G>& vid) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat == _St_ref::_Member) {
        return u.find_vertex_edge(__g, vid);
      } else if constexpr (_Strat == _St_ref::_Non_member) {
        return find_vertex_edge(__g, u, vid); // intentional ADL
      } else if constexpr (_Strat == _St_ref::_Auto_eval) {
        return ranges::find_if(edges(__g, u), [&__g, &vid](auto&& uv) { return target_id(__g, uv) == vid; });
      } else {
        static_assert(_Always_false<_G>,
                      "find_vertex_edge(g,uid) has not been defined and the default implemenation cannot be evaluated");
      }
    }

    /**
     * @brief Find an edge in the graph.
     * 
     * Complexity: O(E), where |E| is the number of outgoing edges of vertex u
     * 
     * Default implementation: find_vertex_edge(g, *find_vertex(g,uid), vid)
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uid The vertex source id of the edge.
     * @param vid The vertex target id of the edge.
     * @return An edge iterator of an outgoing edge of u with a target id of vid. end(edges(g,uid)) will
     *         be returned if an edge doesn't exist.
    */
    template <class _G>
    requires(_Choice_id<_G&>._Strategy != _St_id::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, const vertex_id_t<_G>& uid, const vertex_id_t<_G>& vid) const
          noexcept(_Choice_id<_G&>._No_throw) {
      constexpr _St_id _Strat = _Choice_id<_G&>._Strategy;

      //if constexpr (_Strat == _St_id::_Member) {
      //  return __g.find_vertex_edge(uid);
      //} else
      if constexpr (_Strat == _St_id::_Non_member) {
        return find_vertex_edge(__g, uid, vid); // intentional ADL
      } else if constexpr (_Strat == _St_id::_Auto_eval) {
        return find_vertex_edge(__g, *find_vertex(__g, uid), vid); // default impl
      } else {
        static_assert(_Always_false<_G>,
                      "find_vertex_edge(g,uid) has not been defined and the default implemenation cannot be evaluated");
      }
    }
  };
} // namespace _Find_vertex_edge

inline namespace _Cpos {
  inline constexpr _Find_vertex_edge::_Cpo find_vertex_edge;
}


//
// contains_edge(g,uid,vid) -> bool
//      default = uid < size(vertices(g)) && vid < size(vertices(g)), if adjacency_matrix<G> && is_integral_v<vertex_id_t<G>>
//              = find_vertex_edge(g,uid,vid) != ranges::end(edges(g,uid));
//
namespace _Contains_edge {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void contains_edge() = delete;           // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void contains_edge();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_id_ADL = _Has_class_or_enum_type<_G> //
                        && requires(_G&& __g, const vertex_id_t<_G>& uid, const vertex_id_t<_G>& vid) {
                             { _Fake_copy_init(contains_edge(__g, uid, vid)) }; // intentional ADL
                           };

  template <class _G, class _UnCV>
  concept _Can_eval_matrix_id = _Has_class_or_enum_type<_G>                        //
                                && is_adjacency_matrix_v<_G>                       //
                                && ranges::random_access_range<vertex_range_t<_G>> //
                                && is_integral_v<vertex_id_t<_G>>;

  template <class _G, class _UnCV>
  concept _Can_eval_id = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, vertex_id_t<_G> uid, vertex_id_t<_G> vid) {
                              { _Fake_copy_init(find_vertex_edge(__g, uid, vid)) };
                            };

  class _Cpo {
  private:
    enum class _St_id { _None, _Non_member, _Matrix_eval, _Auto_eval };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_id> _Choose_id() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_id_ADL<_G, _UnCV>) {
        return {_St_id::_Non_member,
                noexcept(_Fake_copy_init(contains_edge(declval<_G>(), declval<vertex_id_t<_G>>(),
                                                       declval<vertex_id_t<_G>>())))}; // intentional ADL
      } else if constexpr (_Can_eval_matrix_id<_G, _UnCV>) {
        return {_St_id::_Matrix_eval, noexcept(vertices(declval<_G>()))};
      } else if constexpr (_Can_eval_id<_G, _UnCV>) {
        return {
              _St_id::_Auto_eval,
              noexcept(_Fake_copy_init(find_vertex_edge(
                    declval<_G>(), declval<vertex_id_t<_G>>(),
                    declval<vertex_id_t<_G>>())))}; // default eval; use find_vertex_edge(g,uid,vid) for noexcept value
      }

      else {
        return {_St_id::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_id> _Choice_id = _Choose_id<_G>();

  public:
    /**
     * @brief Does an edge exist in the graph?
     * 
     * Complexity (default implementations):
     *  O(1), if is_adjacency_matrix_v<G> && is_integral<vertex_id_t<G>>
     *  O(E), where |E| is the number of outgoing edges of vertex u
     * 
     * Default implementations: 
     *  uid < size(vertices(__g) && vid < size(vertices(__g), if is_adjacency_matrix_v<G> && is_integral<vertex_id_t<G>>
     *  find_vertex_edge(g, *ui) != end(edges(g, *ui)),       otherwise
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uid The vertex source id of the edge.
     * @param vid The vertex target id of the edge.
     * @return true if the edge exists, or false otherwise.
    */
    template <class _G>
    requires(_Choice_id<_G&>._Strategy != _St_id::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, const vertex_id_t<_G>& uid, const vertex_id_t<_G>& vid) const
          noexcept(_Choice_id<_G&>._No_throw) {
      constexpr _St_id _Strat = _Choice_id<_G&>._Strategy;

      if constexpr (_Strat == _St_id::_Non_member) {
        return contains_edge(__g, uid, vid); // intentional ADL
      } else if constexpr (_Strat == _St_id::_Matrix_eval) {
        return uid < ranges::size(vertices(__g)) && vid < ranges::size(vertices(__g));
      } else if constexpr (_Strat == _St_id::_Auto_eval) {
        return contains_edge(__g, *find_vertex(__g, uid), vid); // default impl
      } else {
        static_assert(_Always_false<_G>, "contains_edge(g,uid) has not been defined for graph G and the default "
                                         "implemenation cannot be evaluated");
      }
    }
  };
} // namespace _Contains_edge

inline namespace _Cpos {
  inline constexpr _Contains_edge::_Cpo contains_edge;
}


//
// degree(g,u) -> integral
//      default = size(edges(g,u)) if sized_range<vertex_edge_range_t<G>>
//
namespace _Degree {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void degree() = delete;                  // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void degree();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, vertex_reference_t<_G> u) {
                              { _Fake_copy_init(u.degree(__g)) };
                            };
  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const vertex_reference_t<_G>& u) {
                              { _Fake_copy_init(degree(__g, u)) }; // intentional ADL
                            };
  template <class _G, class _UnCV>
  concept _Can_ref_eval = ranges::sized_range<vertex_edge_range_t<_G>> //
                          && requires(_G&& __g, vertex_reference_t<_G> u) {
                               { _Fake_copy_init(edges(__g, u)) };
                             };

  //template <class _G, class _UnCV>
  //concept _Has_id_member = requires(_G&& __g, const vertex_id_t<_G>& uid) {
  //                           { _Fake_copy_init(uid,degree(__g)) };
  //                         };

  template <class _G, class _UnCV>
  concept _Has_id_ADL = _Has_class_or_enum_type<_G> //
                        && requires(_G&& __g, const vertex_id_t<_G>& uid) {
                             { _Fake_copy_init(degree(__g, uid)) }; // intentional ADL
                           };
  template <class _G, class _UnCV>
  concept _Can_id_eval = ranges::sized_range<vertex_edge_range_t<_G>> //
                         && requires(_G&& __g, vertex_id_t<_G> uid) {
                              { _Fake_copy_init(edges(__g, uid)) };
                            };

  class _Cpo {
  private:
    enum class _St_id { _None, _Non_member, _Auto_eval };
    enum class _St_ref { _None, _Member, _Non_member, _Auto_eval };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_id> _Choose_id() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_id_ADL<_G, _UnCV>) {
        return {_St_id::_Non_member,
                noexcept(_Fake_copy_init(degree(declval<_G>(), declval<vertex_id_t<_G>>())))}; // intentional ADL
      } else if constexpr (_Can_id_eval<_G, _UnCV>) {
        return {_St_id::_Auto_eval, noexcept(_Fake_copy_init(ranges::size(
                                          edges(declval<_G>(), declval<vertex_id_t<_G>>()))))}; // default impl
      } else {
        return {_St_id::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_id> _Choice_id = _Choose_id<_G>();

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<vertex_reference_t<_G>>().degree(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {_St_ref::_Non_member,
                noexcept(_Fake_copy_init(degree(declval<_G>(), declval<vertex_reference_t<_G>>())))}; // intentional ADL
      } else if constexpr (_Can_ref_eval<_G, _UnCV>) {
        return {_St_ref::_Auto_eval,
                noexcept(_Fake_copy_init(ranges::size(edges(declval<_G>(), declval<vertex_reference_t<_G>>()))))};
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief The number of outgoing edges of a vertex.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: size(edges(g, u))
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param u A vertex instance.
     * @return The number of outgoing edges of vertex u.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, vertex_reference_t<_G> u) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_id = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_id == _St_ref::_Member) {
        return u.degree(__g);
      } else if constexpr (_Strat_id == _St_ref::_Non_member) {
        return degree(__g, u); // intentional ADL
      } else if constexpr (_Strat_id == _St_ref::_Auto_eval) {
        return ranges::size(edges(__g, u)); // default impl
      } else {
        static_assert(_Always_false<_G>,
                      "degree(g,u) is not defined and the default implementation cannot be evaluated");
      }
    }

    /**
     * @brief Get the outgoing degree of a vertex id.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: degree(g, *find_vertex(g, uid))
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uid Vertex id.
     * @return A range of the outgoing degree.
    */
    template <class _G>
    requires(_Choice_id<_G&>._Strategy != _St_id::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, const vertex_id_t<_G>& uid) const
          noexcept(_Choice_id<_G&>._No_throw) {
      constexpr _St_id _Strat_id = _Choice_id<_G&>._Strategy;

      if constexpr (_Strat_id == _St_id::_Non_member) {
        return degree(__g, uid); // intentional ADL
      } else if constexpr (_Strat_id == _St_id::_Auto_eval) {
        return ranges::size(edges(__g, uid)); // default impl
      } else {
        static_assert(_Always_false<_G>,
                      "degree(g,uid) is not defined and the default implementation cannot be evaluated");
      }
    }
  };
} // namespace _Degree

inline namespace _Cpos {
  inline constexpr _Degree::_Cpo degree;
}


//
// vertex_value(g,u) -> <<user-defined type>>
//
// vertex_value_t<G> = decltype(vertex_value(g,u))
//
namespace _Vertex_value {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void vertex_value() = delete;            // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void vertex_value();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, vertex_reference_t<_G> u) {
                              { _Fake_copy_init(u.vertex_value(__g)) };
                            };
  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const vertex_reference_t<_G>& u) {
                              { _Fake_copy_init(vertex_value(__g, u)) }; // intentional ADL
                            };

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member,
                noexcept(_Fake_copy_init(declval<vertex_reference_t<_G>>().vertex_value(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {_St_ref::_Non_member, noexcept(_Fake_copy_init(vertex_value(
                                            declval<_G>(), declval<vertex_reference_t<_G>>())))}; // intentional ADL
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief The user-defined value for a vertex, if it exists.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: n/a. This must be specialized for the vertex type of each graph type, if available.
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param u A vertex instance.
     * @return The value associated with vertex u.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, vertex_reference_t<_G> u) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_id = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_id == _St_ref::_Member) {
        return u.vertex_value(__g);
      } else if constexpr (_Strat_id == _St_ref::_Non_member) {
        return vertex_value(__g, u); // intentional ADL
      } else {
        static_assert(_Always_false<_G>, "vertex_value(g,u) is not defined");
      }
    }
  };
} // namespace _Vertex_value

inline namespace _Cpos {
  inline constexpr _Vertex_value::_Cpo vertex_value;
}

template <class G>
using vertex_value_t = decltype(vertex_value(declval<G&&>(), declval<vertex_reference_t<G>>()));


//
// edge_value(g,u) -> <<user-defined type>>
//
// edge_value_t<G> = decltype(edge_value(g,u))
//
namespace _Edge_value {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void edge_value() = delete;              // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void edge_value();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g, edge_reference_t<_G> uv) {
                              { _Fake_copy_init(uv.edge_value(__g)) };
                            };
  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g, const edge_reference_t<_G>& uv) {
                              { _Fake_copy_init(edge_value(__g, uv)) }; // intentional ADL
                            };

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<edge_reference_t<_G>>().edge_value(declval<_G>())))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {
              _St_ref::_Non_member,
              noexcept(_Fake_copy_init(edge_value(declval<_G>(), declval<edge_reference_t<_G>>())))}; // intentional ADL
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief The user-defined value for a edge, if it exists.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: n/a. This must be specialized for the edge type of each graph type, if available.
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uv A edge instance.
     * @return The value associated with edge uv.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g, edge_reference_t<_G> uv) const
          noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_id = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_id == _St_ref::_Member) {
        return uv.edge_value(__g);
      } else if constexpr (_Strat_id == _St_ref::_Non_member) {
        return edge_value(__g, uv); // intentional ADL
      } else {
        static_assert(_Always_false<_G>, "edge_value(g,uv) is not defined");
      }
    }
  };
} // namespace _Edge_value

inline namespace _Cpos {
  inline constexpr _Edge_value::_Cpo edge_value;
}

// edge value type
template <class G>
using edge_value_t = decltype(edge_value(declval<G&&>(), declval<edge_reference_t<G>>()));


//
// graph_value(g,u) -> <<user-defined type>>
//
// edge_value_t<G> = decltype(graph_value(g,u))
//
namespace _Graph_value {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
  void graph_value() = delete;             // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
  void graph_value();
#endif                                     // ^^^ workaround ^^^

  template <class _G, class _UnCV>
  concept _Has_ref_member = requires(_G&& __g) {
                              { _Fake_copy_init(__g.graph_value()) };
                            };
  template <class _G, class _UnCV>
  concept _Has_ref_ADL = _Has_class_or_enum_type<_G> //
                         && requires(_G&& __g) {
                              { _Fake_copy_init(graph_value(__g)) }; // intentional ADL
                            };

  class _Cpo {
  private:
    enum class _St_ref { _None, _Member, _Non_member };

    template <class _G>
    [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
      static_assert(is_lvalue_reference_v<_G>);
      using _UnCV = remove_cvref_t<_G>;

      if constexpr (_Has_ref_member<_G, _UnCV>) {
        return {_St_ref::_Member, noexcept(_Fake_copy_init(declval<graph_reference_t<_G>>().graph_value()))};
      } else if constexpr (_Has_ref_ADL<_G, _UnCV>) {
        return {_St_ref::_Non_member, noexcept(_Fake_copy_init(graph_value(declval<_G>())))}; // intentional ADL
      } else {
        return {_St_ref::_None};
      }
    }

    template <class _G>
    static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<_G>();

  public:
    /**
     * @brief The user-defined value for a edge, if it exists.
     * 
     * Complexity: O(1)
     * 
     * Default implementation: n/a. This must be specialized for the edge type of each graph type, if available.
     * 
     * @tparam G The graph type.
     * @param g A graph instance.
     * @param uv A edge instance.
     * @return The value associated with edge uv.
    */
    template <class _G>
    requires(_Choice_ref<_G&>._Strategy != _St_ref::_None)
    [[nodiscard]] constexpr auto operator()(_G&& __g) const noexcept(_Choice_ref<_G&>._No_throw) {
      constexpr _St_ref _Strat_id = _Choice_ref<_G&>._Strategy;

      if constexpr (_Strat_id == _St_ref::_Member) {
        return __g.graph_value();
      } else if constexpr (_Strat_id == _St_ref::_Non_member) {
        return graph_value(__g); // intentional ADL
      } else {
        static_assert(_Always_false<_G>, "graph_value(g) is not defined");
      }
    }
  };
} // namespace _Graph_value

inline namespace _Cpos {
  inline constexpr _Graph_value::_Cpo graph_value;
}

// graph value type
template <class G>
using graph_value_t = decltype(graph_value(declval<G&&>(), declval<graph_reference_t<G>>()));


namespace edgelist {
  //
  // edges(ul)  -> edgelist_range_t<G>
  //
  // edgelist_range_t<EL>    = decltype(edges(declval<EL&&>()));
  // edgelist_iterator_t<EL> = ranges::iterator_t<edgelist_range_t<EL&&>>;
  //
  namespace _Edgelist_edges {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
    void edges() = delete;                 // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
    void edges();
#endif                                     // ^^^ workaround ^^^

    template <class EL>
    concept _Has_ref_ADL = _Has_class_or_enum_type<EL> //
                           && requires(EL&& el) {
                                { _Fake_copy_init(edges(el)) }; // intentional ADL
                              };


    class _Cpo {
    private:
      enum class _St_ref { _None, _Non_member };

      template <class EL>
      [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
        static_assert(is_lvalue_reference_v<EL>);

        if constexpr (_Has_ref_ADL<EL>) {
          return {_St_ref::_Non_member, noexcept(_Fake_copy_init(edges(declval<EL>())))}; // intentional ADL
        } else {
          return {_St_ref::_None};
        }
      }

      template <class EL>
      static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<EL>();

    public:
      /**
       * @brief Get the edgelist.
       * 
       * Complexity: O(1)
       * 
       * Default implementation: n/a. This must be specialized for each edgelist type.
       * 
       * @tparam G The graph type.
       * @param g A graph instance.
       * @param u Vertex reference.
       * @return A range of the outgoing edges.
      */
      template <class EL>
      requires(_Choice_ref<EL&>._Strategy != _St_ref::_None)
      [[nodiscard]] constexpr auto operator()(EL&& el) const noexcept(_Choice_ref<EL&>._No_throw) {
        constexpr _St_ref _Strat_ref = _Choice_ref<EL&>._Strategy;

        if constexpr (_Strat_ref == _St_ref::_Non_member) {
          return edges(el); // intentional ADL
        } else {
          static_assert(_Always_false<EL>, "edgelist::edges(el) is not defined");
        }
      }
    };
  } // namespace _Edgelist_edges

  inline namespace _Cpos {
    inline constexpr _Edgelist_edges::_Cpo edges;
  }

  //namespace tag_invoke {
  //  TAG_INVOKE_DEF(edges); // edges(e) -> [edge list vertices]
  //}

  //template <class E>
  //auto edges(E&& el) -> decltype(tag_invoke::edges(el)) {
  //  return tag_invoke::edges(el);
  //}

  template <class EL> // Use EL for edgelist to avoid ambiguity of E for an edge
  using edgelist_range_t = decltype(edges(declval<EL&&>()));

  template <class EL>
  using edgelist_iterator_t = ranges::iterator_t<edgelist_range_t<EL>>;

  template <class EL>
  using edge_t = ranges::range_value_t<edgelist_range_t<EL>>; // edge value type

  template <class EL>
  using edge_reference_t = ranges::range_reference_t<edgelist_range_t<EL>>; // edge reference type

  //
  // source_id(ul)  -> ?
  //
  // vertex_source_id_t<EL> = decltype(source_id(declval<EL&&>(), declval<edgelist_iterator_t<EL>>()));
  //
  namespace _Edgelist_source_id {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
    void source_id() = delete;             // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
    void source_id();
#endif                                     // ^^^ workaround ^^^

    template <class EL>
    concept _Has_ref_ADL = _Has_class_or_enum_type<EL> //
                           && requires(EL&& el, edgelist_iterator_t<EL> uvi) {
                                { _Fake_copy_init(source_id(el, uvi)) }; // intentional ADL
                              };


    class _Cpo {
    private:
      enum class _St_ref { _None, _Non_member };

      template <class EL>
      [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
        static_assert(is_lvalue_reference_v<EL>);

        if constexpr (_Has_ref_ADL<EL>) {
          return {_St_ref::_Non_member, noexcept(_Fake_copy_init(source_id(
                                              declval<EL>(), declval<edgelist_iterator_t<EL>>())))}; // intentional ADL
        } else {
          return {_St_ref::_None};
        }
      }

      template <class EL>
      static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<EL>();

    public:
      /**
       * @brief Get the edgelist.
       * 
       * Complexity: O(1)
       * 
       * Default implementation: n/a. This must be specialized for each edgelist type.
       * 
       * @tparam G The graph type.
       * @param g A graph instance.
       * @param u Vertex reference.
       * @return A range of the outgoing source_id.
      */
      template <class EL>
      requires(_Choice_ref<EL&>._Strategy != _St_ref::_None)
      [[nodiscard]] constexpr auto operator()(EL&& el, edgelist_iterator_t<EL> uvi) const
            noexcept(_Choice_ref<EL&>._No_throw) {
        constexpr _St_ref _Strat_ref = _Choice_ref<EL&>._Strategy;

        if constexpr (_Strat_ref == _St_ref::_Non_member) {
          return source_id(el, uvi); // intentional ADL
        } else {
          static_assert(_Always_false<EL>, "edgelist::source_id(el,uvi) is not defined");
        }
      }
    };
  } // namespace _Edgelist_source_id

  inline namespace _Cpos {
    inline constexpr _Edgelist_source_id::_Cpo source_id;
  }
  //namespace tag_invoke {
  //  TAG_INVOKE_DEF(vertex_id_source);
  //}

  template <class EL>
  using vertex_id_t = decltype(source_id(declval<EL&&>(), declval<edgelist_iterator_t<EL>>()));

  //
  // target_id(ul)  -> ?
  //
  // vertex_target_id_t<EL> = decltype(target_id(declval<EL&&>(), declval<edgelist_iterator_t<EL>>()));
  //
  namespace _Edgelist_target_id {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
    void target_id() = delete;             // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
    void target_id();
#endif                                     // ^^^ workaround ^^^

    template <class EL>
    concept _Has_ref_ADL = _Has_class_or_enum_type<EL> //
                           && requires(EL&& el, edgelist_iterator_t<EL> uvi) {
                                { _Fake_copy_init(target_id(el, uvi)) }; // intentional ADL
                              };


    class _Cpo {
    private:
      enum class _St_ref { _None, _Non_member };

      template <class EL>
      [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
        static_assert(is_lvalue_reference_v<EL>);

        if constexpr (_Has_ref_ADL<EL>) {
          return {_St_ref::_Non_member, noexcept(_Fake_copy_init(target_id(
                                              declval<EL>(), declval<edgelist_iterator_t<EL>>())))}; // intentional ADL
        } else {
          return {_St_ref::_None};
        }
      }

      template <class EL>
      static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<EL>();

    public:
      /**
       * @brief Get the edgelist.
       * 
       * Complexity: O(1)
       * 
       * Default implementation: n/a. This must be specialized for each edgelist type.
       * 
       * @tparam G The graph type.
       * @param g A graph instance.
       * @param u Vertex reference.
       * @return A range of the outgoing target_id.
      */
      template <class EL>
      requires(_Choice_ref<EL&>._Strategy != _St_ref::_None)
      [[nodiscard]] constexpr auto operator()(EL&& el, edgelist_iterator_t<EL> uvi) const
            noexcept(_Choice_ref<EL&>._No_throw) {
        constexpr _St_ref _Strat_ref = _Choice_ref<EL&>._Strategy;

        if constexpr (_Strat_ref == _St_ref::_Non_member) {
          return target_id(el, uvi); // intentional ADL
        } else {
          static_assert(_Always_false<EL>, "edgelist::target_id(el,uvi) is not defined");
        }
      }
    };
  } // namespace _Edgelist_target_id

  inline namespace _Cpos {
    inline constexpr _Edgelist_target_id::_Cpo target_id;
  }

  //namespace tag_invoke {
  //  TAG_INVOKE_DEF(target_id);
  //}

  //template <class E>
  //auto target_id(E&& el, edgelist_iterator_t<E> e) {
  //  return tag_invoke::target_id(el, e);
  //}

  template <class EL>
  using vertex_target_id_t = decltype(target_id(declval<EL&&>(), declval<edgelist_iterator_t<EL>>()));


  //
  // vertex_id_source(ul)  -> ?
  //
  // vertex_source_id_t<EL> = decltype(vertex_id_source(declval<EL&&>(), declval<edgelist_iterator_t<EL>>()));
  //
  namespace _Edgelist_Vertex_value {
#if defined(__clang__) || defined(__EDG__) // TRANSITION, VSO-1681199
    void vertex_value() = delete;          // Block unqualified name lookup
#else                                      // ^^^ no workaround / workaround vvv
    void vertex_value();
#endif                                     // ^^^ workaround ^^^

    template <class EL>
    concept _Has_ref_ADL = _Has_class_or_enum_type<EL> //
                           && requires(EL&& el, edgelist_iterator_t<EL> uvi) {
                                { _Fake_copy_init(vertex_value(el, uvi)) }; // intentional ADL
                              };


    class _Cpo {
    private:
      enum class _St_ref { _None, _Non_member };

      template <class EL>
      [[nodiscard]] static consteval _Choice_t<_St_ref> _Choose_ref() noexcept {
        static_assert(is_lvalue_reference_v<EL>);

        if constexpr (_Has_ref_ADL<EL>) {
          return {_St_ref::_Non_member, noexcept(_Fake_copy_init(vertex_value(
                                              declval<EL>(), declval<edgelist_iterator_t<EL>>())))}; // intentional ADL
        } else {
          return {_St_ref::_None};
        }
      }

      template <class EL>
      static constexpr _Choice_t<_St_ref> _Choice_ref = _Choose_ref<EL>();

    public:
      /**
       * @brief Get the edgelist.
       * 
       * Complexity: O(1)
       * 
       * Default implementation: n/a. This must be specialized for each edgelist type.
       * 
       * @tparam G The graph type.
       * @param g A graph instance.
       * @param u Vertex reference.
       * @return A range of the outgoing vertex_value.
      */
      template <class EL>
      requires(_Choice_ref<EL&>._Strategy != _St_ref::_None)
      [[nodiscard]] constexpr auto operator()(EL&& el, edgelist_iterator_t<EL> uvi) const
            noexcept(_Choice_ref<EL&>._No_throw) {
        constexpr _St_ref _Strat_ref = _Choice_ref<EL&>._Strategy;

        if constexpr (_Strat_ref == _St_ref::_Non_member) {
          return vertex_value(el, uvi); // intentional ADL
        } else {
          static_assert(_Always_false<EL>, "edgelist::vertex_value(el,uvi) is not defined");
        }
      }
    };
  } // namespace _Edgelist_Vertex_value

  inline namespace _Cpos {
    inline constexpr _Edgelist_Vertex_value::_Cpo vertex_value;
  }

  //namespace tag_invoke {
  //  TAG_INVOKE_DEF(edge_value);
  //}

  //template <class E>
  //auto edge_value(E&& el, edgelist_iterator_t<E> e) {
  //  return tag_invoke::edge_value(el, e);
  //}

  template <class E>
  using edge_value_t = decltype(edge_value(declval<E&&>(), declval<edgelist_iterator_t<E>>()));

  template <class E>
  concept edgelist_range = ranges::forward_range<edgelist_range_t<E>>;

  template <class EL>
  concept edgelist = edgelist_range<EL> //
                     && requires(EL&& el, edge_reference_t<EL> uv) {
                          is_same_v<decltype(source_id(el, uv)), decltype(target_id(el, uv))>;
                        };

} // namespace edgelist

} // namespace std::graph
