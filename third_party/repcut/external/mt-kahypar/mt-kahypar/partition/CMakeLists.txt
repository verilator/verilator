add_subdirectory(preprocessing)
add_subdirectory(coarsening)
add_subdirectory(refinement)
add_subdirectory(initial_partitioning)
add_subdirectory(mapping)
add_subdirectory(registries)

set(PartitionSources
        deep_multilevel.cpp
        partitioner.cpp
        partitioner_facade.cpp
        multilevel.cpp
        context.cpp
        context_enum_classes.cpp
        conversion.cpp
        metrics.cpp
        recursive_bipartitioning.cpp
        )

target_sources(MtKaHyPar-Sources INTERFACE ${PartitionSources})
