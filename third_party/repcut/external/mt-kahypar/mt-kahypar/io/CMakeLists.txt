set(IOSources
        csv_output.cpp
        hypergraph_io.cpp
        hypergraph_factory.cpp
        sql_plottools_serializer.cpp
        partitioning_output.cpp
        presets.cpp
        command_line_options.cpp)

target_sources(MtKaHyPar-Sources INTERFACE ${IOSources})


# create header that contains the project version
set(MT_KAHYPAR_AUTOGEN_WARNING "ATTENTION: this file is auto-generated and should never be modified")
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/version.h.in" "${CMAKE_CURRENT_SOURCE_DIR}/version.h" @ONLY)
