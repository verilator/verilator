cmake_minimum_required(VERSION 3.15)
cmake_policy(SET CMP0091 NEW) # Use MSVC_RUNTIME_LIBRARY to select the runtime

project(Verilator
    VERSION 4.025.99
    HOMEPAGE_URL https://verilator.org
    LANGUAGES CXX
)

include(GNUInstallDirs)
include(CMakePackageConfigHelpers)
include(CheckStructHasMember)

if (WIN32)
    # Check for Chcocolatey winflexbison
    # See https://github.com/lexxmark/winflexbison/releases
    set(WIN_FLEX_BISON C:/ProgramData/chocolatey/lib/winflexbison3/tools)
    if (EXISTS ${WIN_FLEX_BISON})
        list(APPEND CMAKE_PREFIX_PATH ${WIN_FLEX_BISON})
    endif()
endif()

find_package(Perl REQUIRED)
find_package(BISON)
find_package(FLEX)

check_struct_has_member("struct stat.st_mtim" tv_nsec sys/stat.h HAVE_STAT_NSEC LANGUAGE CXX)

set(PACKAGE_NAME ${PROJECT_NAME})
set(PACKAGE_VERSION ${PROJECT_VERSION})

add_subdirectory(src)
