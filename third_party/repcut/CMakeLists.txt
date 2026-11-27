cmake_minimum_required(VERSION 3.15)

project(rcp VERSION 0.2.0)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

include(cmake/MtKaHyPar.cmake)
add_subdirectory(lib)
if(RCP_BUILD_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()
