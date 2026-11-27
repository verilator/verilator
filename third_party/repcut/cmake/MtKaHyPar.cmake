# Scope the dependency settings to the bundled static library.
function(rcp_add_mtkahypar)
    set(BUILD_SHARED_LIBS OFF)
    get_filename_component(KAHYPAR_DEPENDENCY_ROOT "${PROJECT_SOURCE_DIR}/.." ABSOLUTE)
    set(KAHYPAR_SERIAL_INCLUDE_DIR "${PROJECT_SOURCE_DIR}/serial")
    add_subdirectory("${PROJECT_SOURCE_DIR}/external/mt-kahypar"
                     "${PROJECT_BINARY_DIR}/external/mt-kahypar" EXCLUDE_FROM_ALL)
endfunction()

rcp_add_mtkahypar()
