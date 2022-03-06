cmake_minimum_required(VERSION 3.15)
cmake_policy(SET CMP0091 NEW) # Use MSVC_RUNTIME_LIBRARY to select the runtime
find_package(PythonLibs 3.10 REQUIRED)
project(Verilator
    VERSION 4.025.99
    HOMEPAGE_URL https://verilator.org
    LANGUAGES CXX
)

option(CMAKE_UNITY_BUILD
    "Builds concatenated source files, potentially sppeding up the build.")
option(DEBUG_AND_RELEASE_AND_COVERAGE [[
Builds both the debug and release binaries, overriding CMAKE_BUILD_TYPE.
Not supported under MSBuild."]])

set(CMAKE_INSTALL_DATADIR "${CMAKE_INSTALL_PREFIX}/share/verilator")
include(GNUInstallDirs)
include(CMakePackageConfigHelpers)
include(CheckStructHasMember)
include(ExternalProject)

if (WIN32)
    # Check for Chcocolatey winflexbison
    # See https://github.com/lexxmark/winflexbison/releases
    set(WIN_FLEX_BISON C:/ProgramData/chocolatey/lib/winflexbison3/tools)
    if (EXISTS ${WIN_FLEX_BISON})
        list(APPEND CMAKE_PREFIX_PATH ${WIN_FLEX_BISON})
    endif()
endif()

#find_package(Perl REQUIRED)
set(PERL_EXECUTABLE python)
find_package(BISON)
find_package(FLEX)

check_struct_has_member("struct stat.st_mtim" tv_nsec sys/stat.h HAVE_STAT_NSEC LANGUAGE CXX)

#
# Build

set_property(GLOBAL PROPERTY JOB_POOLS one_job=1)

if (DEBUG_AND_RELEASE_AND_COVERAGE)
    if (CMAKE_GENERATOR MATCHES "^Visual Studio ")
        error("%Error: The DEBUG_AND_RELEASE_AND_COVERAGE option is not supported in MSBuild-based builds.")
    endif()
    set(saved_build_type ${CMAKE_BUILD_TYPE})
    set(CMAKE_BUILD_TYPE Debug)
    add_subdirectory(src build-Debug)
    set(CMAKE_BUILD_TYPE Release)
    add_subdirectory(src build-Release)
    set(CMAKE_BUILD_TYPE Coverage)
    add_subdirectory(src build-Coverage)
    set(CMAKE_BUILD_TYPE ${saved_build_type})
else()
    add_subdirectory(src)
endif()

#
# Configuration and Installation

set(PACKAGE_NAME ${PROJECT_NAME})
set(PACKAGE_VERSION ${PROJECT_VERSION})

foreach (_file include/verilated.mk include/verilated_config.h verilator.pc)
    configure_file(${_file}.in ${_file} @ONLY)
endforeach()

configure_package_config_file(verilator-config.cmake.in verilator-config.cmake
    INSTALL_DESTINATION ${CMAKE_INSTALL_DATADIR}
)

configure_package_config_file(verilator-config-version.cmake.in verilator-config-version.cmake
    INSTALL_DESTINATION ${CMAKE_INSTALL_DATADIR}
)

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/verilator.pc DESTINATION ${CMAKE_INSTALL_DATAROOTDIR}/pkgconfig)

add_custom_target(manfiles ALL)

#foreach (program
#    verilator
#    verilator_coverage
#    verilator_gantt
#    verilator_profcfunc
#)
#    set(output ${CMAKE_CURRENT_BINARY_DIR}/${program}.1)
#    install(PROGRAMS bin/${program} TYPE BIN)
#    install(FILES ${output} DESTINATION ${CMAKE_INSTALL_MANDIR}/man1)
#
#    add_custom_command(
#        OUTPUT ${program}.1 MAIN_DEPENDENCY bin/${program}
#	COMMAND C:\\msys64\\usr\\bin\\perl C:\\msys64\\usr\\bin\\core_perl\\pod2man ARGS
#            "$<SHELL_PATH:${CMAKE_CURRENT_SOURCE_DIR}/bin/${program}>"
#            "$<SHELL_PATH:${CMAKE_CURRENT_BINARY_DIR}/${program}.1>"
#    )
#    add_custom_target(${program}_1 DEPENDS ${output})
#    add_dependencies(manfiles ${program}_1)
#endforeach()

install(FILES bin/verilator_includer DESTINATION ${CMAKE_INSTALL_DATADIR}/bin)

install(DIRECTORY examples TYPE DATA FILES_MATCHING
    PATTERN "examples/*/*.[chv]*"
    PATTERN "examples/*/Makefile*"
    PATTERN "examples/*/CMakeLists.txt"
)

install(DIRECTORY include TYPE DATA FILES_MATCHING
    PATTERN "include/verilated_config.h"
    PATTERN "include/verilated.mk"
    PATTERN "include/*.[chv]"
    PATTERN "include/gtkwave/*.[chv]*"
    PATTERN "include/vltstd/*.[chv]*"
)

add_custom_target(info ALL)

#add_custom_command(
#    OUTPUT verilator.txt MAIN_DEPENDENCY bin/verilator
#    COMMAND pod2text ARGS
#        "$<SHELL_PATH:${CMAKE_CURRENT_SOURCE_DIR}/bin/verilator>"
#        "$<SHELL_PATH:${CMAKE_CURRENT_BINARY_DIR}/verilator.txt>"
#)
#add_custom_target(verilator_txt DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/verilator.txt)

#add_custom_command(
#    OUTPUT verilator.html MAIN_DEPENDENCY bin/verilator
#    COMMAND pod2html ARGS
#        --infile "$<SHELL_PATH:${CMAKE_CURRENT_SOURCE_DIR}/bin/verilator>"
#        --outfile "$<SHELL_PATH:${CMAKE_CURRENT_BINARY_DIR}/verilator.html>"
#)
#add_custom_target(verilator_html DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/verilator.html)

#add_dependencies(info verilator_txt verilator_html)

install(FILES
    ${CMAKE_CURRENT_BINARY_DIR}/verilator.txt
    ${CMAKE_CURRENT_BINARY_DIR}/verilator.html
    DESTINATION ${CMAKE_INSTALL_DATADIR}/doc
)
