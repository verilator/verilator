set(DatastructureSources
      graph.cpp
      fixed_vertex_support.cpp)

set(MultilevelDatastructureSources
      static_hypergraph_factory.cpp
      static_hypergraph.cpp)

set(MultilevelGraphDatastructureSources
      static_graph_factory.cpp
      static_graph.cpp)

set(NLevelDatastructureSources
      contraction_tree.cpp
      dynamic_hypergraph.cpp
      dynamic_hypergraph_factory.cpp
      incident_net_array.cpp)

set(NLevelGraphDatastructureSources
      contraction_tree.cpp
      dynamic_graph.cpp
      dynamic_graph_factory.cpp
      dynamic_adjacency_array.cpp)

target_sources(MtKaHyPar-Sources INTERFACE ${DatastructureSources})
target_sources(MtKaHyPar-Sources INTERFACE ${MultilevelDatastructureSources})
target_sources(MtKaHyPar-LibraryBuildSources PRIVATE
    ${MultilevelGraphDatastructureSources}
    ${NLevelDatastructureSources}
    ${NLevelGraphDatastructureSources})
