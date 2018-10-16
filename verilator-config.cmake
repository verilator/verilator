cmake_minimum_required(VERSION 3.8)

#Prefer VERILATOR_ROOT from environment
if (DEFINED ENV{VERILATOR_ROOT})
    set(VERILATOR_ROOT "$ENV{VERILATOR_ROOT}" CACHE PATH "VERILATOR_ROOT")
endif()

set(VERILATOR_ROOT "${CMAKE_CURRENT_LIST_DIR}" CACHE PATH "VERILATOR_ROOT")

find_file(VERILATOR_BIN NAMES verilator_bin verilator_bin.exe HINTS ${VERILATOR_ROOT}/bin NO_CMAKE_PATH NO_CMAKE_ENVIRONMENT_PATH NO_CMAKE_SYSTEM_PATH)

if (NOT VERILATOR_ROOT)
    message(FATAL_ERROR "VERILATOR_ROOT cannot be detected. Set it to the appropriate directory (e.g. /usr/share/verilator) as an environment variable or CMake define.")
endif()

if (NOT VERILATOR_BIN)
    message(FATAL_ERROR "Cannot find verilator_bin excecutable.")
endif()

set(verilator_FOUND 1)

#Check flag support. Skip on MSVC, these are all GCC flags.
if (NOT (DEFINED VERILATOR_CFLAGS OR CMAKE_CXX_COMPILER_ID MATCHES MSVC))
    include(CheckCXXCompilerFlag)
    foreach (FLAG faligned-new fbracket-depth=4096 Qunused-arguments Wno-bool-operation Wno-parentheses-equality
                  Wno-sign-compare Wno-uninitialized Wno-unused-but-set-variable Wno-unused-parameter
                  Wno-unused-variable Wno-shadow)
        string(MAKE_C_IDENTIFIER ${FLAG} FLAGNAME)
        check_cxx_compiler_flag(-${FLAG} ${FLAGNAME})
        if (${FLAGNAME})
            set(VERILATOR_CFLAGS ${VERILATOR_CFLAGS} -${FLAG})
        endif()
    endforeach()
endif()

function(verilate TARGET)
    cmake_parse_arguments(VERILATE "TRACE;SYSTEMC" "NAME;TOP" "SOURCES;ARGS;INCLUDEDIRS;SLOW_FLAGS;FAST_FLAGS" ${ARGN})
    if (NOT VERILATE_TOP)
        list(GET VERILATE_SOURCES 0 TOPSRC)
        get_filename_component(VERILATE_TOP ${TOPSRC} NAME_WE)
    endif()
    if (NOT VERILATE_NAME)
        set(VERILATE_NAME V${VERILATE_TOP})
    endif()

    if (VERILATE_TRACE)
        set(VERILATE_ARGS -trace ${VERILATE_ARGS})
        #If any verilate() call specifies TRACE, define VM_TRACE in the final build
        set_property(TARGET ${TARGET} PROPERTY VERILATOR_TRACE TRUE)
    endif()
    get_property(TRACE TARGET ${TARGET} PROPERTY VERILATOR_TRACE SET)

    if (VERILATE_SYSTEMC)
        set(VERILATE_ARGS ${VERILATE_ARGS} --sc)
    else()
        set(VERILATE_ARGS ${VERILATE_ARGS} --cc)
    endif()

    foreach(D ${VERILATE_INCLUDEDIRS})
        set(VERILATE_ARGS ${VERILATE_ARGS} -y "${D}")
    endforeach()

    set(DIR ${CMAKE_CURRENT_BINARY_DIR}/${VERILATE_NAME})
    file(MAKE_DIRECTORY ${DIR})
    set(VCMAKE ${DIR}/${VERILATE_NAME}.cmake)
    if (NOT EXISTS ${VCMAKE})
        #Create a dummy file, so we reconfigure when the real one is made
        file(WRITE ${VCMAKE} "")
    endif()
    include(${VCMAKE})

    #Reconfigure if file list has changed (check contents rather than modified time to avoid unnecessary reconfiguration)
    add_custom_command(OUTPUT ${VCMAKE}
                       COMMAND ${CMAKE_COMMAND} -E copy_if_different "${VCMAKE}.gen" "${VCMAKE}"
                       DEPENDS ${VCMAKE}.gen)
    add_custom_target(${VERILATE_NAME}.cmake.target ALL DEPENDS ${VCMAKE})

    set(OUTPUTS ${${VERILATE_NAME}_CLASSES_FAST} ${${VERILATE_NAME}_CLASSES_SLOW} ${${VERILATE_NAME}_SUPPORT_FAST} ${${VERILATE_NAME}_SUPPORT_SLOW})

    string(TOLOWER ${CMAKE_CXX_COMPILER_ID} COMPILER)
    if (NOT COMPILER MATCHES "msvc|clang")
        set(COMPILER gcc)
    endif()

    add_custom_command(OUTPUT ${OUTPUTS} ${VCMAKE}.gen
                       COMMAND ${VERILATOR_BIN} -Wall -Wno-fatal --compiler ${COMPILER} --top-module ${VERILATE_TOP} --prefix ${VERILATE_NAME} --Mdir ${DIR} --cmake ${VERILATE_ARGS} ${VERILATE_SOURCES}
                       WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                       DEPENDS ${${VERILATE_NAME}_DEPS} VERBATIM)

    add_dependencies(${TARGET} ${VERILATE_NAME}.cmake.target)
    target_sources(${TARGET} PRIVATE ${OUTPUTS} ${${VERILATE_NAME}_GLOBAL})
    target_include_directories(${TARGET} PRIVATE ${VERILATOR_ROOT}/include ${VERILATOR_ROOT}/include/vltstd ${DIR})
    target_compile_definitions(${TARGET} PRIVATE VL_PRINTF=printf VM_COVERAGE=${${VERILATE_NAME}_COVERAGE} VM_SC=${VM_SC} VM_TRACE=$<BOOL:${TRACE}> $<$<BOOL:${${VERILATE_NAME}_THREADS}>:VL_THREADED>)
    target_compile_options(${TARGET} PRIVATE ${VERILATOR_CFLAGS})
    set_source_files_properties(${${VERILATE_NAME}_CLASSES_SLOW} ${${VERILATE_NAME}_SUPPORT_SLOW} PROPERTIES COMPILE_FLAGS "${VERILATE_SLOW_FLAGS}")
    set_source_files_properties(${${VERILATE_NAME}_CLASSES_FAST} ${${VERILATE_NAME}_SUPPORT_FAST} PROPERTIES COMPILE_FLAGS "${VERILATE_FAST_FLAGS}")
endfunction(verilate)
