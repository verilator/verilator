# DESCRIPTION: Verilator: Bundled RepCut compiler dependency
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

cmake_minimum_required(VERSION 3.15)
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
    project(VerilatorRepCut LANGUAGES C CXX)
    if(NOT CMAKE_BUILD_TYPE)
        set(CMAKE_BUILD_TYPE Release)
    endif()
endif()

# Keep these settings local to the dependency subtree. In particular, its
# C++17 requirement and exception support must not change compiler/runtime flags.
option(RCP_BUILD_TESTS "Build bundled RepCut API tests" OFF)
if(RCP_BUILD_TESTS)
    enable_testing()
endif()
set(KAHYPAR_ENABLE_EXTENDED_INSTRUCTIONS OFF)
set(KAHYPAR_ENABLE_ARCH_COMPILE_OPTIMIZATIONS OFF)
if(MSVC)
    set(CMAKE_MSVC_RUNTIME_LIBRARY "MultiThreaded$<$<CONFIG:Debug>:DebugDLL>")
endif()
find_package(Threads REQUIRED)
add_subdirectory(repcut EXCLUDE_FROM_ALL)

# The GNU Make compiler build consumes the same archives and system libraries
# as the CMake build. The public boundary is repcut.h's C interface.
if(UNIX AND NOT CMAKE_CONFIGURATION_TYPES)
    set(repcut_link_flags
        "\"$<TARGET_FILE:repcut>\"\n\"$<TARGET_FILE:mtkahypar>\"\n${CMAKE_THREAD_LIBS_INIT}\n$<JOIN:$<GENEX_EVAL:$<TARGET_PROPERTY:MtKaHyPar-BuildFlags,INTERFACE_LINK_OPTIONS>>,\n>\n"
    )
    file(
        GENERATE OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/repcut-libs.rsp"
        CONTENT "${repcut_link_flags}"
    )
endif()
