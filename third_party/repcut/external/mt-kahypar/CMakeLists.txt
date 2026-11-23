cmake_minimum_required(VERSION 3.15)
list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules)

# define the project version
set(MT_KAHYPAR_VERSION "1.7")
set(MTKAHYPAR_INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/include")

project(MtKaHyPar
        VERSION ${MT_KAHYPAR_VERSION}
        DESCRIPTION "Mt-KaHyPar: Multi-Threaded Karlsruhe Hypergraph Partitioning"
        LANGUAGES CXX C)


#################################################################
## Sanity checks and policies                                  ##
#################################################################

if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "Debug" "Release" "RelWithDebInfo")
  message(FATAL_ERROR "CMAKE_BUILD_TYPE must be set. Options are: Debug, Release, RelWithDebInfo")
endif()
if("${PROJECT_SOURCE_DIR}" STREQUAL "${PROJECT_BINARY_DIR}")
  message(FATAL_ERROR "Build directory must be different from source directory.")
endif()

#################################################################
## Meta targets                                               ##
#################################################################

# meta targets for flags
add_library(MtKaHyPar-BuildFlags INTERFACE)
target_compile_features(MtKaHyPar-BuildFlags INTERFACE cxx_std_17)

# meta targets for includes and source files
add_library(MtKaHyPar-Include INTERFACE)
target_include_directories(MtKaHyPar-Include INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})

add_library(MtKaHyPar-Sources INTERFACE)

# meta target for library build, which must be built with all features enabled
add_library(MtKaHyPar-LibraryBuildSources OBJECT "")
target_link_libraries(MtKaHyPar-LibraryBuildSources PRIVATE MtKaHyPar-Sources)
target_link_libraries(MtKaHyPar-LibraryBuildSources PUBLIC MtKaHyPar-Include MtKaHyPar-BuildFlags)
target_compile_definitions(MtKaHyPar-LibraryBuildSources PUBLIC MT_KAHYPAR_LIBRARY_MODE
                           KAHYPAR_ENABLE_LARGE_K_PARTITIONING_FEATURES KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
                           KAHYPAR_ENABLE_SOED_METRIC KAHYPAR_ENABLE_STEINER_TREE_METRIC)


#################################################################
## Options                                                     ##
#################################################################

# specific compile features/build properties
option(KAHYPAR_USE_64_BIT_IDS "Enables 64-bit vertex and hyperedge IDs." OFF)
option(KAHYPAR_USE_ADDRESS_SANITIZER "Adds address sanitizer to compile options." OFF)
option(KAHYPAR_ENABLE_EXTENDED_INSTRUCTIONS "Allows instructions that might not be fully portable: `-mcx16 -msse4.2 -mcrc32`" OFF)
option(KAHYPAR_ENABLE_ARCH_COMPILE_OPTIMIZATIONS "Adds the compile flags `-mtune=native -march=native`, or `/arch:AVX` for `MSVC`" OFF)

option(KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES "Enable experimental algorithms." OFF)

# assertions
option(KAHYPAR_DISABLE_ASSERTIONS "Disable all internal assertions." OFF)
option(KAHYPAR_USE_STANDARD_ASSERTIONS "Use standard C++ asserts instead of custom assertions." OFF)
option(KAHYPAR_ENABLE_HEAVY_PREPROCESSING_ASSERTIONS "Enable heavy assertions in preprocessing phase." OFF)
option(KAHYPAR_ENABLE_HEAVY_COARSENING_ASSERTIONS "Enable heavy assertions in coarsening phase." OFF)
option(KAHYPAR_ENABLE_HEAVY_INITIAL_PARTITIONING_ASSERTIONS "Enable heavy assertions in initial partitioning phase." OFF)
option(KAHYPAR_ENABLE_HEAVY_REFINEMENT_ASSERTIONS "Enable heavy assertions in refinement phase." OFF)

# developer build options
option(KAHYPAR_CI_BUILD "Indicate that this build is executed on GitHub Actions." OFF)
option(KAHYPAR_USE_GCOV "Compile and run tests with gcov for coverage analysis." OFF)


#################################################################
## Print header with most important infos                      ##
#################################################################

if(CMAKE_BUILD_TYPE)
  # normalize so that exactly the first letter is uppercase
  string(TOUPPER "${CMAKE_BUILD_TYPE}" BUILD_TYPE_UPPER)
  string(TOLOWER "${CMAKE_BUILD_TYPE}" BUILD_TYPE_LOWER)
  string(SUBSTRING "${BUILD_TYPE_UPPER}" 0 1 FIRST_LETTER)
  string(SUBSTRING "${BUILD_TYPE_LOWER}" 1 -1 REMAINDER)
  set(KAHYPAR_BUILD_DESCRIPTION "${FIRST_LETTER}${REMAINDER} Build")
  if (KAHYPAR_ENABLE_ARCH_COMPILE_OPTIMIZATIONS AND NOT BUILD_TYPE_UPPER MATCHES "DEBUG")
    set(KAHYPAR_BUILD_DESCRIPTION "${KAHYPAR_BUILD_DESCRIPTION} + march=native")
  endif()
  message(STATUS "Mt-KaHyPar: ${KAHYPAR_BUILD_DESCRIPTION}, static serial library")
endif()


#################################################################
## Compatibility checks which interact with options            ##
#################################################################

if(UNIX)
  include(CheckIncludeFiles)
  set(CMAKE_REQUIRED_QUIET TRUE)
  set(KAHYPAR_REQUIRED_HEADERS "unistd.h" "sys/mman.h" "sys/ioctl.h")
  check_include_files("${KAHYPAR_REQUIRED_HEADERS}" KAHYPAR_HEADERS_AVAILABLE LANGUAGE CXX)
  if(NOT KAHYPAR_HEADERS_AVAILABLE)
    message(FATAL_ERROR "The following system headers are required, but some are not available: ${KAHYPAR_REQUIRED_HEADERS}")
  endif()

elseif(NOT WIN32)
  message(FATAL_ERROR "Only unix-based operating systems and windows are supported.")
endif()


#################################################################
## Options that translate into compile flags                   ##
#################################################################

if(KAHYPAR_DISABLE_ASSERTIONS)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_DISABLE_ASSERTIONS)
endif(KAHYPAR_DISABLE_ASSERTIONS)

if(KAHYPAR_USE_STANDARD_ASSERTIONS)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_USE_STANDARD_ASSERTIONS)
endif(KAHYPAR_USE_STANDARD_ASSERTIONS)

if(KAHYPAR_ENABLE_HEAVY_PREPROCESSING_ASSERTIONS)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_ENABLE_HEAVY_PREPROCESSING_ASSERTIONS)
endif(KAHYPAR_ENABLE_HEAVY_PREPROCESSING_ASSERTIONS)

if(KAHYPAR_ENABLE_HEAVY_COARSENING_ASSERTIONS)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_ENABLE_HEAVY_COARSENING_ASSERTIONS)
endif(KAHYPAR_ENABLE_HEAVY_COARSENING_ASSERTIONS)

if(KAHYPAR_ENABLE_HEAVY_INITIAL_PARTITIONING_ASSERTIONS)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_ENABLE_HEAVY_INITIAL_PARTITIONING_ASSERTIONS)
endif(KAHYPAR_ENABLE_HEAVY_INITIAL_PARTITIONING_ASSERTIONS)

if(KAHYPAR_ENABLE_HEAVY_REFINEMENT_ASSERTIONS)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_ENABLE_HEAVY_REFINEMENT_ASSERTIONS)
endif(KAHYPAR_ENABLE_HEAVY_REFINEMENT_ASSERTIONS)

if(KAHYPAR_USE_64_BIT_IDS)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_USE_64_BIT_IDS)
endif(KAHYPAR_USE_64_BIT_IDS)

if(KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES)
endif(KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES)

target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_DISABLE_HWLOC KAHYPAR_DISABLE_PARLAY)


#################################################################
## Compile options and specialized builds                      ##
#################################################################

if (CMAKE_SYSTEM_PROCESSOR MATCHES "(x86)|(X86)|(amd64)|(AMD64)")
    set(KAHYPAR_X86 TRUE)
else()
    set(KAHYPAR_X86 FALSE)
endif()

# Add compile flags that enable warnings
if(NOT MSVC)
  target_compile_options(MtKaHyPar-BuildFlags INTERFACE
      -W -Wall -Wextra -Wunused -Wuninitialized -Wfatal-errors -Wcast-qual
      -Woverloaded-virtual -Wredundant-decls -Wno-unused-function
      -Winit-self -pedantic -Wno-unused-function
  )
else()
  target_compile_options(MtKaHyPar-BuildFlags INTERFACE
      /W3
      /wd4267 /wd4244 # percision loss
      /wd4334 # result of 32-bit shift implicitly converted to 64 bits
      /wd4146 # unary minus operator applied to unsigned type
      /permissive-
  )
endif()

if(KAHYPAR_USE_GCOV AND NOT MSVC)
  # add coverage anaylsis compile and link flags
  target_compile_options(MtKaHyPar-BuildFlags INTERFACE -fprofile-arcs -ftest-coverage -fprofile-update=atomic)
  target_link_options(MtKaHyPar-BuildFlags INTERFACE -lgcov --coverage)
endif()

if(NOT MSVC)
  target_compile_options(MtKaHyPar-BuildFlags INTERFACE
      $<$<CONFIG:Release>:-O3>
      $<$<OR:$<CONFIG:Debug>,$<CONFIG:RelWithDebInfo>>:
          -g3
          -UNDEBUG # keep assertions activated
      >
      $<$<CONFIG:Debug>:-fno-omit-frame-pointer>
  )
else()
  target_compile_options(MtKaHyPar-BuildFlags INTERFACE
      /bigobj
      $<$<CONFIG:Release>:/O2>
      $<$<OR:$<CONFIG:Debug>,$<CONFIG:RelWithDebInfo>>:
          /Zi
          /UNDEBUG # keep assertions activated
      >
      $<$<CONFIG:Debug>:/Oy->
  )
endif()

if(WIN32)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE
      NOMINMAX # disable min/max macros as they clash with the standard library
      NOGDI # avoid pulling in the ERROR macro
      WIN32_LEAN_AND_MEAN # we only need process, thread, file and console support
      _CRT_SECURE_NO_WARNINGS # supress unsafe standard lib function usage warnings
  )
endif()

if(UNIX)
  target_compile_options(MtKaHyPar-BuildFlags INTERFACE $<$<CONFIG:DEBUG>:-fsanitize=undefined>)
  target_link_options(MtKaHyPar-BuildFlags INTERFACE $<$<CONFIG:DEBUG>:-fsanitize=undefined>)
endif()

if (KAHYPAR_X86 AND KAHYPAR_ENABLE_EXTENDED_INSTRUCTIONS)
  include(CheckCXXCompilerFlag)
  include(CheckISAExtensions)
  block()
    set(CMAKE_REQUIRED_QUIET TRUE)
    check_cxx_compiler_flag(-mcx16 KAHYPAR_HAS_MCX16)
  endblock()
  block()
    set(CMAKE_REQUIRED_QUIET TRUE)
    check_cxx_compiler_flag(-mcrc32 KAHYPAR_HAS_CRC32)
  endblock()

  if(KAHYPAR_HAS_MCX16)
    target_compile_options(MtKaHyPar-BuildFlags INTERFACE -mcx16)
  endif()
  if(KAHYPAR_HAS_CRC32)
    target_compile_options(MtKaHyPar-BuildFlags INTERFACE -mcrc32)
  endif()
  if(SUPPORTS_SSE4_2)
    if(NOT MSVC)
      target_compile_options(MtKaHyPar-BuildFlags INTERFACE -msse4.2)
    else()
      target_compile_options(MtKaHyPar-BuildFlags INTERFACE /arch:SSE4.2)
      if(NOT (KAHYPAR_ENABLE_ARCH_COMPILE_OPTIMIZATIONS AND SUPPORTS_AVX))
        # AVX enables unchecked use of popcnt within the STL already
        target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE
            MT_KAHYPAR_MSVC_USE_POPCNT_INTRINSICS
        )
      endif()
    endif()
  endif()
endif()

# check this after include(CheckISAExtensions)
if (KAHYPAR_ENABLE_STEINER_TREE_METRIC AND KAHYPAR_X86
    AND KAHYPAR_ENABLE_EXTENDED_INSTRUCTIONS AND SUPPORTS_SSE4_2)
    # growt requires SSE instructions
    set(KAHYPAR_USE_GROWT TRUE)
else()
    set(KAHYPAR_USE_GROWT FALSE)
endif()

if(KAHYPAR_ENABLE_ARCH_COMPILE_OPTIMIZATIONS)
  if(NOT MSVC)
    target_compile_options(MtKaHyPar-BuildFlags INTERFACE
        $<$<CONFIG:Release>:-march=native -mtune=native>
        $<$<CONFIG:RelWithDebInfo>:-march=native -mtune=native>
    )
  else()
    if(SUPPORTS_AVX)
      # MSVC marks popcnt as generally available only if AVX is supported
      target_compile_options(MtKaHyPar-BuildFlags INTERFACE /arch:AVX)
    endif()
  endif()
endif()

if(KAHYPAR_USE_ADDRESS_SANITIZER AND (NOT KAHYPAR_CI_BUILD))
  if(NOT MSVC)
    target_compile_options(MtKaHyPar-BuildFlags INTERFACE
        $<$<CONFIG:Debug>:-fsanitize=address>
    )
    target_link_options(MtKaHyPar-BuildFlags INTERFACE
        $<$<CONFIG:Debug>:-fsanitize=address>
    )
  else()
    target_compile_options(MtKaHyPar-BuildFlags INTERFACE
        $<$<CONFIG:Debug>:/fsanitize=address>
    )
    target_link_options(MtKaHyPar-BuildFlags INTERFACE
        $<$<CONFIG:Debug>:/fsanitize=address>
    )
  endif()
endif()


#################################################################
## Setup of dependencies                                       ##
#################################################################

# Pinned local dependencies; the bundled build never downloads sources.
add_subdirectory("${KAHYPAR_DEPENDENCY_ROOT}/cli11"
                 "${CMAKE_CURRENT_BINARY_DIR}/cli11" EXCLUDE_FROM_ALL)
target_link_libraries(MtKaHyPar-Include INTERFACE CLI11::CLI11)
target_include_directories(MtKaHyPar-Include INTERFACE
    "${KAHYPAR_DEPENDENCY_ROOT}/kahypar-shared-resources"
    "${KAHYPAR_DEPENDENCY_ROOT}")
target_include_directories(MtKaHyPar-Include BEFORE INTERFACE "${KAHYPAR_SERIAL_INCLUDE_DIR}")
target_compile_definitions(MtKaHyPar-Include INTERFACE REPCUT_SERIAL_PARTITIONER=1)

add_subdirectory(lib)
add_subdirectory(dependencies)
add_subdirectory(mt-kahypar)
add_library(MtKaHyPar::mtkahypar ALIAS mtkahypar)
