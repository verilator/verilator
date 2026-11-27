set(RefinementSources
        fm/fm_commons.cpp
        fm/multitry_kway_fm.cpp
        fm/localized_kway_fm_core.cpp
        fm/global_rollback.cpp
        fm/sequential_twoway_fm_refiner.cpp
        label_propagation/label_propagation_refiner.cpp
        rebalancing/advanced_rebalancer.cpp
        rebalancing/deterministic_rebalancer.cpp
        rebalancing/repair_empty_blocks.cpp
        deterministic/deterministic_label_propagation.cpp
        deterministic/deterministic_jet_refiner.cpp
        flows/problem_construction.cpp
        flows/flow_refinement_scheduler.cpp
        flows/active_block_scheduler.cpp
        flows/quotient_graph.cpp
        flows/flow_refiner.cpp
        flows/sequential_construction.cpp
        flows/parallel_construction.cpp
        flows/flow_hypergraph_builder.cpp
        flows/deterministic/deterministic_flow_refinement_scheduler.cpp
        flows/deterministic/participation_scheduler.cpp
        )

set(Km1Sources
        gains/km1/km1_gain_cache.cpp)

set(SoedSources
        gains/soed/soed_gain_cache.cpp)

set(CutSources
        gains/cut/cut_gain_cache.cpp)

set(CutGraphSources
        gains/cut_for_graphs/cut_gain_cache_for_graphs.cpp)

set(SteinerTreeSources
        gains/steiner_tree/steiner_tree_gain_cache.cpp
        gains/steiner_tree/steiner_tree_flow_network_construction.cpp)

set(SteinerTreeGraphSources
        gains/steiner_tree_for_graphs/steiner_tree_gain_cache_for_graphs.cpp
        gains/steiner_tree_for_graphs/steiner_tree_flow_network_construction_for_graphs.cpp)

target_sources(MtKaHyPar-Sources INTERFACE ${RefinementSources})
target_sources(MtKaHyPar-Sources INTERFACE ${Km1Sources})
target_sources(MtKaHyPar-Sources INTERFACE ${CutSources})

if ( KAHYPAR_ENABLE_SOED_METRIC )
  target_sources(MtKaHyPar-Sources INTERFACE ${SoedSources})
else ()
  target_sources(MtKaHyPar-LibraryBuildSources PRIVATE ${SoedSources})
endif()

if ( KAHYPAR_ENABLE_STEINER_TREE_METRIC )
  target_sources(MtKaHyPar-Sources INTERFACE ${SteinerTreeSources})
else ()
  target_sources(MtKaHyPar-LibraryBuildSources PRIVATE ${SteinerTreeSources})
endif()

if ( KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES )
  target_sources(MtKaHyPar-Sources INTERFACE ${CutGraphSources})
  if ( KAHYPAR_ENABLE_STEINER_TREE_METRIC )
    target_sources(MtKaHyPar-Sources INTERFACE ${SteinerTreeGraphSources})
  else ()
    target_sources(MtKaHyPar-LibraryBuildSources PRIVATE ${SteinerTreeGraphSources})
  endif()
else ()
  target_sources(MtKaHyPar-LibraryBuildSources PRIVATE ${CutGraphSources})
  target_sources(MtKaHyPar-LibraryBuildSources PRIVATE ${SteinerTreeGraphSources})
endif()
