#include <catch2/catch.hpp>
#include "csv_routes.hpp"
#include "graph/graph.hpp"
#include "graph/algorithm/mst.hpp"
#include "graph/container/dynamic_graph.hpp"
#include "graph/container/utility_edgelist.hpp"
#ifdef _MSC_VER
#  include "Windows.h"
#endif

using std::cout;
using std::endl;

using std::graph::vertex_t;
using std::graph::vertex_id_t;
using std::graph::vertex_reference_t;
using std::graph::vertex_iterator_t;
using std::graph::vertex_edge_range_t;
using std::graph::edge_t;
using std::graph::edge_reference_t;
using std::graph::edge_value_t;

using std::graph::vertices;
using std::graph::edges;
using std::graph::vertex_value;
using std::graph::target_id;
using std::graph::target;
using std::graph::edge_value;
using std::graph::find_vertex;
using std::graph::vertex_id;

using routes_vol_graph_traits = std::graph::container::vol_graph_traits<double, std::string, std::string>;
using routes_vol_graph_type   = std::graph::container::dynamic_adjacency_graph<routes_vol_graph_traits>;

using edgelist = std::graph::container::
      utility_edgelist<vertex_id_t<routes_vol_graph_type>, vertex_id_t<routes_vol_graph_type>, double>;

TEST_CASE("Kruskal Min ST Algorithm", "[min st]") {
  init_console();
  using G  = routes_vol_graph_type;
  auto&& g = load_graph<G>(TEST_DATA_ROOT_DIR "germany_routes.csv");

  size_t N(size(vertices(g)));
  size_t M = 0;
  for (auto&& [uid, u] : std::graph::views::vertexlist(g)) {
    M += std::graph::degree(g, u);
  }

  edgelist e, t;

  auto evf = [&g](edge_reference_t<G> uv) { return edge_value(g, uv); };
  for (auto&& [uid, vid, uv] : std::graph::views::edgelist(g)) {
    e.push_back(std::make_tuple(uid, vid, evf(uv)));
  }

  //Replace with whatever conforms to std::graph::edgelist
  std::graph::kruskal(e, t);
  double last = -1;
  for (auto&& [u, v, val] : t) {
    REQUIRE(val > last);
    last = val;
    //cout << u << " " << v << " " << val << endl;
  }
}

TEST_CASE("Kruskal Max ST Algorithm", "[max st]") {
  init_console();
  using G  = routes_vol_graph_type;
  auto&& g = load_graph<G>(TEST_DATA_ROOT_DIR "germany_routes.csv");

  size_t N(size(vertices(g)));
  size_t M = 0;
  for (auto&& [uid, u] : std::graph::views::vertexlist(g)) {
    M += std::graph::degree(g, u);
  }

  edgelist e, t;

  auto evf = [&g](edge_reference_t<G> uv) { return edge_value(g, uv); };
  for (auto&& [uid, vid, uv] : std::graph::views::edgelist(g)) {
    e.push_back(std::make_tuple(uid, vid, evf(uv)));
  }

  //Replace with whatever conforms to std::graph::edgelist
  std::graph::kruskal(e, t, [](auto&& i, auto&& j) { return i > j; });
  double last = std::numeric_limits<double>::max();
  for (auto&& [u, v, val] : t) {
    REQUIRE(val < last);
    last = val;
    //cout << u << " " << v << " " << val << endl;
  }
}

TEST_CASE("Prim Min ST Algorithm", "[prim min st]") {
  init_console();
  using G  = routes_vol_graph_type;
  auto&& g = load_ordered_graph<G>(TEST_DATA_ROOT_DIR "germany_routes.csv", name_order_policy::source_order_found);

  std::vector<vertex_id_t<G>> preds(size(vertices(g)));
  std::vector<double>         weights(size(vertices(g)));
  std::graph::prim(g, preds, weights);
  double treeweight = 0;
  for (auto&& [uid, u] : std::graph::views::vertexlist(g)) {
    //cout << "pred of " << uid << " is " << preds[uid] << " with val " << weights[uid] << endl;
    treeweight += weights[uid];
  }
  REQUIRE(treeweight == 1361);
}

TEST_CASE("Prim Max ST Algorithm", "[prim max st]") {
  init_console();
  using G  = routes_vol_graph_type;
  auto&& g = load_ordered_graph<G>(TEST_DATA_ROOT_DIR "germany_routes.csv", name_order_policy::source_order_found);

  std::vector<vertex_id_t<G>> preds(size(vertices(g)));
  std::vector<double>         weights(size(vertices(g)));

  std::graph::prim(
        g, preds, weights, [](auto&& i, auto&& j) { return i > j; }, 0);
  double treeweight = 0;
  for (auto&& [uid, u] : std::graph::views::vertexlist(g)) {
    //cout << "pred of " << uid << " is " << preds[uid] << " with val " << weights[uid] << endl;
    treeweight += weights[uid];
  }
  REQUIRE(treeweight == 1779);
}
