#*****************************************************************************
#
# DESCRIPTION: Script for build tool cmake on both unix and windows
#
#*****************************************************************************
#
# Copyright 2003-2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
#****************************************************************************/

#
# Utilities
macro (addBuildType sourceConfig newConfig)
    get_cmake_property(variableNames VARIABLES)
    foreach (variableName ${variableNames})
        if (variableName MATCHES "^CMAKE_.*_${sourceConfig}(|_.*)$")
            string(REPLACE _${sourceConfig} _${newConfig} newVariableName ${variableName})
            set(${newVariableName} ${${variableName}})
            mark_as_advanced(${newVariableName})
            message(DEBUG "   Propagating ${variableName} to ${newVariableName} = ${${newVariableName}}")
        endif()
    endforeach()
endmacro()

#
# Sources and headers for the verilator binary

set(HEADERS
    V3Active.h
    V3ActiveTop.h
    V3Assert.h
    V3AssertPre.h
    V3Ast.h
    V3AstInlines.h
    V3AstNodeDType.h
    V3AstNodeExpr.h
    V3AstNodeOther.h
    V3AstUserAllocator.h
    V3Begin.h
    V3Branch.h
    V3Broken.h
    V3CCtors.h
    V3CUse.h
    V3Case.h
    V3Cast.h
    V3Class.h
    V3Clean.h
    V3Clock.h
    V3Combine.h
    V3Common.h
    V3Config.h
    V3Const.h
    V3Coverage.h
    V3CoverageJoin.h
    V3Dead.h
    V3Delayed.h
    V3Depth.h
    V3DepthBlock.h
    V3Descope.h
    V3Dfg.h
    V3DfgOptimizer.h
    V3DfgPasses.h
    V3DfgPeephole.h
    V3DfgVertices.h
    V3DupFinder.h
    V3EmitC.h
    V3EmitCBase.h
    V3EmitCConstInit.h
    V3EmitCFunc.h
    V3EmitCMain.h
    V3EmitCMake.h
    V3EmitMk.h
    V3EmitV.h
    V3EmitXml.h
    V3Error.h
    V3Expand.h
    V3File.h
    V3FileLine.h
    V3Force.h
    V3Fork.h
    V3FunctionTraits.h
    V3Gate.h
    V3Global.h
    V3Graph.h
    V3GraphAlg.h
    V3GraphPathChecker.h
    V3GraphStream.h
    V3Hash.h
    V3Hasher.h
    V3HierBlock.h
    V3Inline.h
    V3Inst.h
    V3InstrCount.h
    V3Interface.h
    V3LangCode.h
    V3LanguageWords.h
    V3Life.h
    V3LifePost.h
    V3LinkCells.h
    V3LinkDot.h
    V3LinkInc.h
    V3LinkJump.h
    V3LinkLValue.h
    V3LinkLevel.h
    V3LinkParse.h
    V3LinkResolve.h
    V3List.h
    V3Localize.h
    V3MemberMap.h
    V3MergeCond.h
    V3Mutex.h
    V3Name.h
    V3Name.h
    V3Number.h
    V3OptionParser.h
    V3Options.h
    V3Order.h
    V3OrderGraph.h
    V3OrderMoveGraph.h
    V3Os.h
    V3PairingHeap.h
    V3Param.h
    V3Parse.h
    V3ParseImp.h
    V3ParseSym.h
    V3Partition.h
    V3PartitionGraph.h
    V3PchAstMT.h
    V3PchAstNoMT.h
    V3PreLex.h
    V3PreProc.h
    V3PreShell.h
    V3Premit.h
    V3ProtectLib.h
    V3Randomize.h
    V3Reloop.h
    V3Rtti.h
    V3Sched.h
    V3Scope.h
    V3Scoreboard.h
    V3SenExprBuilder.h
    V3SenTree.h
    V3Simulate.h
    V3Slice.h
    V3Split.h
    V3SplitAs.h
    V3SplitVar.h
    V3Stats.h
    V3StdFuture.h
    V3String.h
    V3Subst.h
    V3SymTable.h
    V3TSP.h
    V3Table.h
    V3Task.h
    V3ThreadPool.h
    V3ThreadSafety.h
    V3Timing.h
    V3Trace.h
    V3TraceDecl.h
    V3Tristate.h
    V3Undriven.h
    V3UniqueNames.h
    V3Unknown.h
    V3Unroll.h
    V3VariableOrder.h
    V3Waiver.h
    V3Width.h
    V3WidthCommit.h
    V3WidthRemove.h
    VlcBucket.h
    VlcOptions.h
    VlcPoint.h
    VlcSource.h
    VlcTest.h
    VlcTop.h
)

set(COMMON_SOURCES
    Verilator.cpp
    V3Active.cpp
    V3ActiveTop.cpp
    V3Assert.cpp
    V3AssertPre.cpp
    V3Ast.cpp
    V3AstNodes.cpp
    V3Begin.cpp
    V3Branch.cpp
    V3Broken.cpp
    V3CCtors.cpp
    V3CUse.cpp
    V3Case.cpp
    V3Cast.cpp
    V3Class.cpp
    V3Clean.cpp
    V3Clock.cpp
    V3Combine.cpp
    V3Common.cpp
    V3Config.cpp
    V3Const__gen.cpp
    V3Coverage.cpp
    V3CoverageJoin.cpp
    V3Dead.cpp
    V3Delayed.cpp
    V3Depth.cpp
    V3DepthBlock.cpp
    V3Descope.cpp
    V3Dfg.cpp
    V3DfgAstToDfg.cpp
    V3DfgDecomposition.cpp
    V3DfgDfgToAst.cpp
    V3DfgOptimizer.cpp
    V3DfgPasses.cpp
    V3DfgPeephole.cpp
    V3DupFinder.cpp
    V3Timing.cpp
    V3EmitCBase.cpp
    V3EmitCConstPool.cpp
    V3EmitCFunc.cpp
    V3EmitCHeaders.cpp
    V3EmitCImp.cpp
    V3EmitCInlines.cpp
    V3EmitCMain.cpp
    V3EmitCMake.cpp
    V3EmitCModel.cpp
    V3EmitCPch.cpp
    V3EmitCSyms.cpp
    V3EmitMk.cpp
    V3EmitV.cpp
    V3EmitXml.cpp
    V3Error.cpp
    V3Expand.cpp
    V3File.cpp
    V3FileLine.cpp
    V3Force.cpp
    V3Fork.cpp
    V3Gate.cpp
    V3Global.cpp
    V3Graph.cpp
    V3GraphAcyc.cpp
    V3GraphAlg.cpp
    V3GraphPathChecker.cpp
    V3GraphTest.cpp
    V3Hash.cpp
    V3Hasher.cpp
    V3HierBlock.cpp
    V3Inline.cpp
    V3Inst.cpp
    V3InstrCount.cpp
    V3Interface.cpp
    V3Life.cpp
    V3LifePost.cpp
    V3LinkCells.cpp
    V3LinkDot.cpp
    V3LinkInc.cpp
    V3LinkJump.cpp
    V3LinkLevel.cpp
    V3LinkLValue.cpp
    V3LinkParse.cpp
    V3LinkResolve.cpp
    V3Localize.cpp
    V3MergeCond.cpp
    V3Name.cpp
    V3Number.cpp
    V3OptionParser.cpp
    V3Options.cpp
    V3Order.cpp
    V3Os.cpp
    V3Param.cpp
    V3Partition.cpp
    V3PreShell.cpp
    V3Premit.cpp
    V3ProtectLib.cpp
    V3Randomize.cpp
    V3Reloop.cpp
    V3Sched.cpp
    V3SchedAcyclic.cpp
    V3SchedPartition.cpp
    V3SchedReplicate.cpp
    V3SchedTiming.cpp
    V3SchedVirtIface.cpp
    V3Scope.cpp
    V3Scoreboard.cpp
    V3Slice.cpp
    V3Split.cpp
    V3SplitAs.cpp
    V3SplitVar.cpp
    V3Stats.cpp
    V3StatsReport.cpp
    V3String.cpp
    V3Subst.cpp
    V3Table.cpp
    V3Task.cpp
    V3ThreadPool.cpp
    V3Trace.cpp
    V3TraceDecl.cpp
    V3Tristate.cpp
    V3TSP.cpp
    V3Undriven.cpp
    V3Unknown.cpp
    V3Unroll.cpp
    V3VariableOrder.cpp
    V3Waiver.cpp
    V3Width.cpp
    V3WidthCommit.cpp
    V3WidthSel.cpp
    V3ParseImp.cpp
    V3ParseGrammar.cpp
    V3ParseLex.cpp
    V3PreProc.cpp
)

SET(COVERAGE_SOURCES
    VlcMain.cpp
)

# Note about tests:
# VlcMain.cpp #includes the following files:
#  V3Error.cpp, V3String.cpp, V3Os.cpp and VlcTop.cpp
# V3Number_test.cpp #includes the following files:
#  V3FileLine.cpp

#
# Generated sources and headers for the verilator binary

set(srcdir ${CMAKE_CURRENT_SOURCE_DIR})

file(TO_NATIVE_PATH ${srcdir}/astgen ASTGEN)
file(TO_NATIVE_PATH ${srcdir}/bisonpre BISONPRE)
file(TO_NATIVE_PATH ${srcdir}/flexfix FLEXFIX)
file(TO_NATIVE_PATH ${srcdir}/../bin/verilator_includer VERILATOR_INCLUDER)
file(TO_NATIVE_PATH ${srcdir}/vlcovgen VLCOVGEN)
file(TO_NATIVE_PATH ${srcdir}/config_rev CONFIG_REV)

configure_file(config_package.h.in config_package.h @ONLY)

add_custom_command(
    OUTPUT V3Ast__gen_forward_class_decls.h V3Dfg__gen_forward_class_decls.h
    DEPENDS ./V3Ast.h ${ASTGEN}
    COMMAND ${PYTHON3} ARGS
    ${ASTGEN} -I "${srcdir}" --astdef V3AstNodeDType.h --astdef V3AstNodeExpr.h --astdef V3AstNodeOther.h --dfgdef V3DfgVertices.h --classes
)
list(APPEND GENERATED_FILES V3Ast__gen_forward_class_decls.h V3Dfg__gen_forward_class_decls.h)
# Output used directly by the `verilator` target

set(verilog_y "${srcdir}/verilog.y" )
set(BISON_V3ParseBison_OUTPUT_HEADER "${CMAKE_CURRENT_BINARY_DIR}/V3ParseBison.h")
set(BISON_V3ParseBison_OUTPUT_SOURCE "${CMAKE_CURRENT_BINARY_DIR}/V3ParseBison.c")
add_custom_command(
    OUTPUT V3ParseBison.c V3ParseBison.h
    MAIN_DEPENDENCY ./verilog.y
    DEPENDS ${BISONPRE}
    COMMAND ${PYTHON3} ARGS
        ${BISONPRE} --yacc "${BISON_EXECUTABLE}" -d -v
            -o "${BISON_V3ParseBison_OUTPUT_SOURCE}" "${verilog_y}"
)
list(APPEND GENERATED_FILES V3ParseBison.c V3ParseBison.h)
# Output used directly by the `verilator` target

set(verilog_l "${srcdir}/verilog.l")
set(FLEX_V3Lexer_pregen_OUTPUTS "${CMAKE_CURRENT_BINARY_DIR}/V3Lexer_pregen.yy.cpp")
add_custom_command(
    OUTPUT V3Lexer_pregen.yy.cpp
    MAIN_DEPENDENCY ./verilog.l
    DEPENDS ${BISON_V3ParseBison_OUTPUT_HEADER} ${HEADERS}
    COMMAND ${FLEX_EXECUTABLE} ARGS
        ${LFLAGS} -o "${FLEX_V3Lexer_pregen_OUTPUTS}" "${verilog_l}"
)
# Output used by another command

set(FLEX_V3Lexer_OUTPUTS ${CMAKE_CURRENT_BINARY_DIR}/V3Lexer.yy.cpp)
add_custom_command(
    OUTPUT V3Lexer.yy.cpp
    MAIN_DEPENDENCY ${FLEX_V3Lexer_pregen_OUTPUTS}
    DEPENDS ${FLEXFIX}
    COMMAND ${PYTHON3} ARGS
        ${FLEXFIX} V3Lexer < "$<SHELL_PATH:${FLEX_V3Lexer_pregen_OUTPUTS}>" > "$<SHELL_PATH:${FLEX_V3Lexer_OUTPUTS}>"
)
add_custom_target(V3Lexer_yy_cpp${CMAKE_BUILD_TYPE} DEPENDS ${FLEX_V3Lexer_OUTPUTS})
# Output included by another source file

set(FLEX_V3PreLex_pregen_OUTPUTS ${CMAKE_CURRENT_BINARY_DIR}/V3PreLex_pregen.yy.cpp)
add_custom_command(
    OUTPUT V3PreLex_pregen.yy.cpp
    MAIN_DEPENDENCY ./V3PreLex.l
    DEPENDS ${HEADERS}
    COMMAND ${FLEX_EXECUTABLE} ARGS
        ${LFLAGS} -o "${FLEX_V3PreLex_pregen_OUTPUTS}" "${srcdir}/V3PreLex.l"
)
# Output used by another command

set(FLEX_V3PreLex_OUTPUTS ${CMAKE_CURRENT_BINARY_DIR}/V3PreLex.yy.cpp)
add_custom_command(
    OUTPUT V3PreLex.yy.cpp
    MAIN_DEPENDENCY ${FLEX_V3PreLex_pregen_OUTPUTS}
    DEPENDS ${FLEXFIX}
    COMMAND ${PYTHON3} ARGS
        ${FLEXFIX} V3PreLex < "$<SHELL_PATH:${FLEX_V3PreLex_pregen_OUTPUTS}>" > "$<SHELL_PATH:${FLEX_V3PreLex_OUTPUTS}>"
)
add_custom_target(V3PreLex_yy_cpp${CMAKE_BUILD_TYPE} DEPENDS ${FLEX_V3PreLex_OUTPUTS})
# Output included by another source file

set(gitHead ${srcdir}/../.git/logs/HEAD)
if (NOT EXISTS ${githead})
    set(gitHead "")
endif()
add_custom_command(
    OUTPUT config_rev.h
    MAIN_DEPENDENCY ${gitHead}
    DEPENDS ${CONFIG_REV}
    COMMAND ${PYTHON3} ARGS
        ${CONFIG_REV} "${srcdir}" > "$<SHELL_PATH:${CMAKE_CURRENT_BINARY_DIR}/config_rev.h>"
)
list(APPEND GENERATED_FILES config_rev.h)
# Output used directly by the `verilator` target

set(ASTGENERATED_NAMES
    V3Const
)

foreach(astgen_name ${ASTGENERATED_NAMES})
    add_custom_command(
        OUTPUT ${astgen_name}__gen.cpp
        MAIN_DEPENDENCY ${astgen_name}.cpp
        DEPENDS ${ASTGEN} V3Ast.h
        COMMAND ${PYTHON3} ARGS
            ${ASTGEN} -I "${srcdir}" --astdef V3AstNodeDType.h --astdef V3AstNodeExpr.h --astdef V3AstNodeOther.h --dfgdef V3DfgVertices.h ${astgen_name}.cpp
    )
    list(APPEND GENERATED_FILES ${astgen_name}__gen.cpp)
endforeach()

#
# Set up the Coverage build type

addBuildType(DEBUG COVERAGE)

# This regenerates include/verilated_cov_key.h in the source tree.
# It is a custom_target, not custom_command, because vlcovgen.d is
# a phony target (it doesn't exist as a file).
add_custom_target(
    vlcovgen.d${CMAKE_BUILD_TYPE}
    DEPENDS ../include/verilated_cov_key.h ${VLCOVGEN}
    COMMENT "Updating include/verilated_cov_key.h"
    COMMAND ${PYTHON3}
        ${VLCOVGEN} --srcdir ${srcdir}
)

#
# Set up the verilator binary target

set(verilator verilator${CMAKE_BUILD_TYPE})

add_executable(${verilator}
    $<$<NOT:$<CONFIG:COVERAGE>>:${COMMON_SOURCES}>
    $<$<NOT:$<CONFIG:COVERAGE>>:${GENERATED_FILES}>
    $<$<CONFIG:COVERAGE>:${COVERAGE_SOURCES} config_rev.h>
)

set_target_properties(${verilator} PROPERTIES
    OUTPUT_NAME_RELEASE   verilator_bin
    OUTPUT_NAME_DEBUG     verilator_bin_dbg
    OUTPUT_NAME_COVERAGE  verilator_coverage_bin_dbg
    #UNITY_BUILD $<IF:$<CONFIG:DEBUG>,FALSE,${CMAKE_UNITY_BUILD}>
    MSVC_RUNTIME_LIBRARY  MultiThreaded$<IF:$<CONFIG:Release>,,DebugDLL>
    #JOB_POOL_LINK         one_job      # Linking takes lots of resources
    INTERPROCEDURAL_OPTIMIZATION_RELEASE  $<IF:MINGW,FALSE,TRUE>
)

add_dependencies(${verilator}
    V3Lexer_yy_cpp${CMAKE_BUILD_TYPE}
    V3PreLex_yy_cpp${CMAKE_BUILD_TYPE}
)

# verilated_cov_key.h is only regenerated in a single-configuration environment.
# This limitation can be lifted when `add_dependencies` will support generator
# expressions. See https://gitlab.kitware.com/cmake/cmake/issues/19467
if (CMAKE_BUILD_TYPE STREQUAL Coverage)
    add_dependencies(${verilator} vlcovgen.d${CMAKE_BUILD_TYPE})
endif()

if (NOT MSVC)
    target_compile_features(${verilator} PRIVATE cxx_std_11)
endif()

target_compile_definitions(${verilator} PRIVATE
    YYDEBUG # Required to get nice error messages
    $<$<CONFIG:DEBUG>:VL_DEBUG>
    $<$<CONFIG:DEBUG>:_GLIBCXX_DEBUG>
)

target_include_directories(${verilator}
    PRIVATE
    ../include
    ${WIN_FLEX_BISON}
    ${CMAKE_CURRENT_BINARY_DIR}
    ${CMAKE_CURRENT_BINARY_DIR}/../include
    ${CMAKE_CURRENT_SOURCE_DIR}
)

if (WIN32)
    if(MINGW)
        target_compile_options(${verilator} PRIVATE -Wa,-mbig-obj)
        target_link_options(${verilator} PRIVATE -Wl,--stack,10000000 -mconsole -lcomctl32 -DWIN_32_LEAN_AND_MEAN)
    else()
        target_compile_options(${verilator} PRIVATE /bigobj)
        target_link_options(${verilator} PRIVATE /STACK:10000000)
    endif()

    target_compile_definitions(${verilator} PRIVATE
        YY_NO_UNISTD_H
    )
    target_include_directories(${verilator} PRIVATE ../platform/win32)
    target_link_libraries(${verilator} PRIVATE bcrypt psapi)
endif()

install(TARGETS ${verilator})
