add_executable(test-library test_library.cpp)
target_link_libraries(test-library PRIVATE repcut)
add_test(NAME library-external-disabled
    COMMAND test-library external-disabled "${CMAKE_CURRENT_BINARY_DIR}/external-disabled")
add_executable(test-hypergraph test_hypergraph.cpp)
target_link_libraries(test-hypergraph PRIVATE repcut)
add_test(NAME hypergraph-merge
    COMMAND test-hypergraph "${CMAKE_CURRENT_BINARY_DIR}/hypergraph")
# Inspect the actual parsed context against the pinned upstream definition.
# Production code uses only MtKaHyPar's public C API.
add_executable(test-mtkahypar-config test_mtkahypar_config.cpp)
target_link_libraries(test-mtkahypar-config PRIVATE repcut MtKaHyPar-Include MtKaHyPar-BuildFlags)
target_compile_definitions(test-mtkahypar-config PRIVATE MT_KAHYPAR_LIBRARY_MODE)
add_test(NAME mtkahypar-low-memory-config
    COMMAND test-mtkahypar-config "${CMAKE_CURRENT_BINARY_DIR}/config with spaces")
add_test(NAME library-repeat-1t
    COMMAND test-library repeat "${CMAKE_CURRENT_BINARY_DIR}/repeat-1t" 1)
add_test(NAME library-serial-only
    COMMAND test-library serial-only "${CMAKE_CURRENT_BINARY_DIR}/serial-only")
set_tests_properties(library-external-disabled PROPERTIES TIMEOUT 40)
add_executable(test-memory test_memory.cpp)
target_link_libraries(test-memory PRIVATE repcut)
add_test(NAME library-memory
    COMMAND ${CMAKE_COMMAND} -DTEST=$<TARGET_FILE:test-memory>
    -DWORK=${CMAKE_CURRENT_BINARY_DIR}/memory -P ${CMAKE_CURRENT_SOURCE_DIR}/test_memory.cmake)

add_executable(test-serial test_serial.cpp)
target_include_directories(test-serial PRIVATE "${PROJECT_SOURCE_DIR}/serial")
target_compile_definitions(test-serial PRIVATE REPCUT_SERIAL_PARTITIONER=1)
add_test(NAME serial-primitives COMMAND test-serial)
