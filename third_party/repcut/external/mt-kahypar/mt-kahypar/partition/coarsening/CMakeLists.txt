set(MultilevelCoarseningSources
        multilevel/deterministic_multilevel_coarsener.cpp
        multilevel/multilevel_uncoarsener.cpp
        multilevel/concurrent_clustering_data.cpp
        multilevel/two_hop_clustering.cpp)

set(NLevelCoarseningSources
        nlevel/nlevel_uncoarsener.cpp)

target_sources(MtKaHyPar-Sources INTERFACE ${MultilevelCoarseningSources})

if(KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES)
  target_sources(MtKaHyPar-Sources INTERFACE ${NLevelCoarseningSources})
else()
  target_sources(MtKaHyPar-LibraryBuildSources PRIVATE ${NLevelCoarseningSources})
endif()
