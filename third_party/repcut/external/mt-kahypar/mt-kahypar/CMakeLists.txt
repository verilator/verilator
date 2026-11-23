add_subdirectory(partition)
add_subdirectory(parallel)
add_subdirectory(datastructures)
add_subdirectory(io)
add_subdirectory(utils)

# Precompiled headers are an optional build optimization (CMake 3.16+).
if(COMMAND target_precompile_headers)
  target_precompile_headers(MtKaHyPar-Sources INTERFACE definitions.h)
  target_precompile_headers(MtKaHyPar-Sources INTERFACE partition/context.h)
endif()
