cmake_minimum_required(VERSION 3.12)
project(WHFC)

if(NOT TARGET TBB::tbb)
    find_package(TBB REQUIRED)
endif()

set(CMAKE_CXX_STANDARD 20)

if(MSVC)
    add_compile_options(
        /W3
        /permissive-
        /wd4244 /wd4267 # suppress percision loss warnings
    )

    add_compile_options(
        "$<$<CONFIG:Debug>:/Zi>"
    )

    add_compile_options(
        "$<$<CONFIG:Release>:/O2>"
    )
else()
    add_compile_options(
        -Wall
        -Wpedantic
        -Wunused
    )

    add_compile_options(
        "$<$<CONFIG:Debug>:-g>"
        "$<$<CONFIG:Debug>:-fno-omit-frame-pointer>"
    )

    add_compile_options(
        "$<$<CONFIG:Release>:-O3>"
        "$<$<CONFIG:Release>:-mtune=native>"
        "$<$<CONFIG:Release>:-march=native>"
    )

    link_libraries(m)
endif()

add_executable(WHFC main.cpp)
target_link_libraries(WHFC PUBLIC TBB::tbb TBB::tbbmalloc)

add_executable(TESTS run_tests.cpp)
target_link_libraries(TESTS PUBLIC TBB::tbb TBB::tbbmalloc)

if(NOT MSVC)
    add_executable(SnapshotTester snapshot_tester.cpp)
    target_link_libraries(SnapshotTester PUBLIC TBB::tbb TBB::tbbmalloc)

    add_executable(FlowTester flow_tester.cpp)
    target_link_libraries(FlowTester PUBLIC TBB::tbb TBB::tbbmalloc)
endif()
