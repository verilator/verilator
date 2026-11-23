add_library(repcut STATIC)

target_sources(
    repcut

    PRIVATE
    ClusterGraph.cpp
    ConeTrie.cpp
    DAG.cpp
    Util.cpp
    RepCut.cpp
    RepCutPartitioner.cpp
    )

find_package(Threads REQUIRED)
target_link_libraries(repcut Threads::Threads)

# Embed the pinned default preset so installed/static consumers do not need
# to locate a configuration file in the source tree or install prefix.
set(mt_preset "${PROJECT_SOURCE_DIR}/external/mt-kahypar/config/default_preset.ini")
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS "${mt_preset}")
file(READ "${mt_preset}" RCP_MTKAHYPAR_PRESET)
string(APPEND RCP_MTKAHYPAR_PRESET "\np-louvain-low-memory-contraction=true\n")
configure_file("${PROJECT_SOURCE_DIR}/cmake/MtKaHyParPreset.h.in"
    "${CMAKE_CURRENT_BINARY_DIR}/MtKaHyParPreset.h" @ONLY)
target_include_directories(repcut PRIVATE "${CMAKE_CURRENT_BINARY_DIR}")
target_sources(repcut PRIVATE MtKaHyPar.cpp)
target_link_libraries(repcut MtKaHyPar::mtkahypar)

# Expose the public header on the include path within the source tree.
# Only repcut.h is the public ABI; the other headers under include/ are
# internal to the library.
target_include_directories(repcut PUBLIC
    ${PROJECT_SOURCE_DIR}/include)
