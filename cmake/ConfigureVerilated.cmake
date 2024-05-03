# *****************************************************************************
#
# DESCRIPTION: Utility CMake functions
#
# *****************************************************************************
#
# Copyright 2003-2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
# ****************************************************************************/

include(CheckCXXCompilerFlag)

function(check_flag result flag)
  set(${result} PARENT_SCOPE)
  check_cxx_compiler_flag(${flag} "CXX_SUPPORT${flag}")

  if(${CXX_SUPPORT${flag}})
    set(${result} ${flag} PARENT_SCOPE)
  endif()
endfunction()

function(check_flag_list result)
  foreach(flag IN LISTS ARGN)
    check_flag(flag_result ${flag})
    list(APPEND flags ${flag_result})
  endforeach()

  string(REPLACE ";" " " flags "${flags}")
  set(${result} ${flags} PARENT_SCOPE)
endfunction()

function(check_set result)
  foreach(flag IN LISTS ARGN)
    check_flag(flag_result ${flag})
    set(${result} ${flag_result} PARENT_SCOPE)

    if(flag_result)
      return()
    endif()
  endforeach()
endfunction()

function(configure_verilated_mk mk_path_in mk_path_out)
  set(AR ${CMAKE_AR})
  set(CXX ${CMAKE_CXX_COMPILER})
  set(LINK ${CMAKE_CXX_COMPILER})
  set(OBJCACHE ${CMAKE_CXX_COMPILER_LAUNCHER})

  find_package(Perl)
  set(PERL ${PERL_EXECUTABLE})
  set(PYTHON3 ${Python3_EXECUTABLE})

  set(CFG_WITH_CCWARN "no")

  if(ENABLE_CCWARN)
    set(CFG_WITH_CCWARN "yes")
  endif()

  set(CFG_WITH_LONGTESTS "no")

  if(ENABLE_LONGTESTS)
    set(CFG_WITH_LONGTESTS "yes")
  endif()

  check_flag(CFG_CXXFLAGS_PROFILE "-pg")

  check_set(CFG_CXXFLAGS_STD_NEWEST
    "-std=gnu++17"
    "-std=c++17"
    "-std=gnu++14"
    "-std=c++14"
  )

  check_flag_list(CFG_CXXFLAGS_NO_UNUSED
    "-faligned-new"
    "-fbracket-depth=4096"
    "-fcf-protection=none"
    "-mno-cet"
    "-Qunused-arguments"
    "-Wno-bool-operation"
    "-Wno-c++11-narrowing"
    "-Wno-constant-logical-operand"
    "-Wno-non-pod-varargs"
    "-Wno-parentheses-equality"
    "-Wno-shadow"
    "-Wno-sign-compare"
    "-Wno-tautological-bitwise-compare"
    "-Wno-tautological-compare"
    "-Wno-uninitialized"
    "-Wno-unused-but-set-parameter"
    "-Wno-unused-but-set-variable"
    "-Wno-unused-parameter"
    "-Wno-unused-variable"
  )

  check_flag_list(CFG_CXXFLAGS_WEXTRA
    "-Wextra"
    "-Wfloat-conversion"
    "-Wlogical-op"
    "-Wthread-safety"
  )

  check_set(CFG_CXXFLAGS_COROUTINES
    "-fcoroutines-ts"
    "-fcoroutines"
  )

  set(CFG_CXXFLAGS_PCH_I "-include")

  if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    set(CGF_GCH_IF_CLANG ".gch")
  endif()

  check_flag_list(CFG_LDLIBS_THREADS
    "-mt"
    "-pthread"
    "-lpthread"
    "-latomic"
  )

  configure_file(${mk_path_in} ${mk_path_out} @ONLY)
endfunction()
