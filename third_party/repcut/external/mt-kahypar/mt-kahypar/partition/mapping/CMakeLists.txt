set(MappingSources
        target_graph.cpp
        all_pair_shortest_path.cpp
        steiner_tree.cpp
        greedy_mapping.cpp
        initial_mapping.cpp
        kerninghan_lin.cpp
        )

target_sources(MtKaHyPar-LibraryBuildSources PRIVATE ${MappingSources})
