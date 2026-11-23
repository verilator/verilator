set(RegistrySources
        register_memory_pool.cpp
        register_refinement_algorithms.cpp
        register_policies.cpp
        register_coarsening_algorithms.cpp
        register_initial_partitioning_algorithms.cpp
        )

target_sources(MtKaHyPar-Sources INTERFACE ${RegistrySources})
