// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2013-2024 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "sv_vpi_user.h"
#include "vpi_user.h"

// Avoid C++11 in this file as not all simulators allow it

//======================================================================

class TestVpiHandle {
    /// For testing, etc, wrap vpiHandle in an auto-releasing class
    vpiHandle m_handle;  // No = as no C++11
    bool m_freeit;  // No = as no C++11

public:
    TestVpiHandle()
        : m_handle(NULL)
        , m_freeit(true) {}
    TestVpiHandle(vpiHandle h)
        : m_handle(h)
        , m_freeit(true) {}
    ~TestVpiHandle() { release(); }
    operator vpiHandle() const { return m_handle; }
    TestVpiHandle& operator=(vpiHandle h) {
        release();
        m_handle = h;
        m_freeit = true;
        return *this;
    }
    void release() {
        if (m_handle && m_freeit) {
            // Below not VL_DO_DANGLING so is portable
#ifdef IVERILOG
            vpi_free_object(m_handle);
#else
            vpi_release_handle(m_handle);
#endif
            m_handle = NULL;
        }
    }
    // Freed by another action e.g. vpi_scan; so empty and don't free again
    void freed() {
        m_handle = NULL;
        m_freeit = false;
    }
};

//======================================================================
// VerilatedVpiError Methods

const char* strFromVpiVal(PLI_INT32 vpiVal) {
    // clang-format off
    static const char* const names[] = {
        "*undefined*",
        "vpiBinStrVal",
        "vpiOctStrVal",
        "vpiDecStrVal",
        "vpiHexStrVal",
        "vpiScalarVal",
        "vpiIntVal",
        "vpiRealVal",
        "vpiStringVal",
        "vpiVectorVal",
        "vpiStrengthVal",
        "vpiTimeVal",
        "vpiObjTypeVal",
        "vpiSuppressVal",
        "vpiShortIntVal",
        "vpiLongIntVal",
        "vpiShortRealVal",
        "vpiRawTwoStateVal",
        "vpiRawFourStateVal",
    };
    // clang-format on
    if ((vpiVal < 0)) return names[0];
    return names[(vpiVal <= vpiRawFourStateVal) ? vpiVal : 0];
}
const char* strFromVpiObjType(PLI_INT32 vpiVal) {
    // clang-format off
    static const char* const names[] = {
        "*undefined*",
        "vpiAlways",
        "vpiAssignStmt",
        "vpiAssignment",
        "vpiBegin",
        "vpiCase",
        "vpiCaseItem",
        "vpiConstant",
        "vpiContAssign",
        "vpiDeassign",
        "vpiDefParam",
        "vpiDelayControl",
        "vpiDisable",
        "vpiEventControl",
        "vpiEventStmt",
        "vpiFor",
        "vpiForce",
        "vpiForever",
        "vpiFork",
        "vpiFuncCall",
        "vpiFunction",
        "vpiGate",
        "vpiIf",
        "vpiIfElse",
        "vpiInitial",
        "vpiIntegerVar",
        "vpiInterModPath",
        "vpiIterator",
        "vpiIODecl",
        "vpiMemory",
        "vpiMemoryWord",
        "vpiModPath",
        "vpiModule",
        "vpiNamedBegin",
        "vpiNamedEvent",
        "vpiNamedFork",
        "vpiNet",
        "vpiNetBit",
        "vpiNullStmt",
        "vpiOperation",
        "vpiParamAssign",
        "vpiParameter",
        "vpiPartSelect",
        "vpiPathTerm",
        "vpiPort",
        "vpiPortBit",
        "vpiPrimTerm",
        "vpiRealVar",
        "vpiReg",
        "vpiRegBit",
        "vpiRelease",
        "vpiRepeat",
        "vpiRepeatControl",
        "vpiSchedEvent",
        "vpiSpecParam",
        "vpiSwitch",
        "vpiSysFuncCall",
        "vpiSysTaskCall",
        "vpiTableEntry",
        "vpiTask",
        "vpiTaskCall",
        "vpiTchk",
        "vpiTchkTerm",
        "vpiTimeVar",
        "vpiTimeQueue",
        "vpiUdp",
        "vpiUdpDefn",
        "vpiUserSystf",
        "vpiVarSelect",
        "vpiWait",
        "vpiWhile",
        "vpiCondition",
        "vpiDelay",
        "vpiElseStmt",
        "vpiForIncStmt",
        "vpiForInitStmt",
        "vpiHighConn",
        "vpiLhs",
        "vpiIndex",
        "vpiLeftRange",
        "vpiLowConn",
        "vpiParent",
        "vpiRhs",
        "vpiRightRange",
        "vpiScope",
        "vpiSysTfCall",
        "vpiTchkDataTerm",
        "vpiTchkNotifier",
        "vpiTchkRefTerm",
        "vpiArgument",
        "vpiBit",
        "vpiDriver",
        "vpiInternalScope",
        "vpiLoad",
        "vpiModDataPathIn",
        "vpiModPathIn",
        "vpiModPathOut",
        "vpiOperand",
        "vpiPortInst",
        "vpiProcess",
        "vpiVariables",
        "vpiUse",
        "vpiExpr",
        "vpiPrimitive",
        "vpiStmt",
        "vpiAttribute",
        "vpiBitSelect",
        "vpiCallback",
        "vpiDelayTerm",
        "vpiDelayDevice",
        "vpiFrame",
        "vpiGateArray",
        "vpiModuleArray",
        "vpiPrimitiveArray",
        "vpiNetArray",
        "vpiRange",
        "vpiRegArray",
        "vpiSwitchArray",
        "vpiUdpArray",
        "vpiActiveTimeFormat",
        "vpiInTerm",
        "vpiInstanceArray",
        "vpiLocalDriver",
        "vpiLocalLoad",
        "vpiOutTerm",
        "vpiPorts",
        "vpiSimNet",
        "vpiTaskFunc",
        "vpiContAssignBit",
        "vpiNamedEventArray",
        "vpiIndexedPartSelect",
        "vpiBaseExpr",
        "vpiWidthExpr",
        "vpiGenScopeArray",
        "vpiGenScope",
        "vpiGenVar",
        "vpiAutomatics"
    };
    static const char* const sv_names1[] = {
        "vpiPackage",
        "vpiInterface",
        "vpiProgram",
        "vpiInterfaceArray",
        "vpiProgramArray",
        "vpiTypespec",
        "vpiModport",
        "vpiInterfaceTfDecl",
        "vpiRefObj",
        "vpiTypeParameter",
        "vpiLongIntVar",
        "vpiShortIntVar",
        "vpiIntVar",
        "vpiShortRealVar",
        "vpiByteVar",
        "vpiClassVar",
        "vpiStringVar",
        "vpiEnumVar",
        "vpiStructVar",
        "vpiUnionVar",
        "vpiBitVar",
        "vpiClassObj",
        "vpiChandleVar",
        "vpiPackedArrayVar",
        "*undefined*",  // 624 is not defined for object types
        "vpiLongIntTypespec",
        "vpiShortRealTypespec",
        "vpiByteTypespec",
        "vpiShortIntTypespec",
        "vpiIntTypespec",
        "vpiClassTypespec",
        "vpiStringTypespec",
        "vpiChandleTypespec",
        "vpiEnumTypespec",
        "vpiEnumConst",
        "vpiIntegerTypespec",
        "vpiTimeTypespec",
        "vpiRealTypespec",
        "vpiStructTypespec",
        "vpiUnionTypespec",
        "vpiBitTypespec",
        "vpiLogicTypespec",
        "vpiArrayTypespec",
        "vpiVoidTypespec",
        "vpiTypespecMember",
        "vpiDistItem",
        "vpiAliasStmt",
        "vpiThread",
        "vpiMethodFuncCall",
        "vpiMethodTaskCall",
        "vpiClockingBlock",
        "vpiClockingIODecl",
        "vpiClassDefn",
        "vpiConstraint",
        "vpiConstraintOrdering",
        "vpiPropertyDecl",
        "vpiPropertySpec",
        "vpiPropertyExpr",
        "vpiMulticlockSequenceExpr",
        "vpiClockedSeq",
        "vpiPropertyInst",
        "vpiSequenceDecl",
        "vpiCaseProperty",
        "*undefined*", // 663 is not defined for object types
        "vpiSequenceInst",
        "vpiImmediateAssert",
        "vpiReturn",
        "vpiAnyPattern",
        "vpiTaggedPattern",
        "vpiStructPattern",
        "vpiDoWhile",
        "vpiOrderedWait",
        "vpiWaitFork",
        "vpiDisableFork",
        "vpiExpectStmt",
        "vpiForeachStmt",
        "vpiFinal",
        "vpiExtends",
        "vpiDistribution",
        "vpiSeqFormalDecl",
        "vpiEnumNet",
        "vpiIntegerNet",
        "vpiTimeNet",
        "vpiStructNet",
        "vpiBreak",
        "vpiContinue",
        "vpiAssert",
        "vpiAssume",
        "vpiCover",
        "vpiDisableCondition",
        "vpiClockingEvent",
        "vpiReturnStmt",
        "vpiPackedArrayTypespec",
        "vpiPackedArrayNet",
        "vpiImmediateAssume",
        "vpiImmediateCover",
        "vpiSequenceTypespec",
        "vpiPropertyTypespec",
        "vpiEventTypespec",
        "vpiPropFormalDecl",
    };
    // clang-format on
    if (vpiVal < 0)
        return names[0];
    else if (vpiVal <= vpiAutomatics)
        return names[vpiVal];
    else if (vpiVal >= vpiPackage && vpiVal <= vpiPropFormalDecl)
        return sv_names1[(vpiVal - vpiPackage)];
    else
        return names[0];
}
const char* strFromVpiMethod(PLI_INT32 vpiVal) {
    // clang-format off
    static const char* const names[] = {
        "vpiCondition",
        "vpiDelay",
        "vpiElseStmt",
        "vpiForIncStmt",
        "vpiForInitStmt",
        "vpiHighConn",
        "vpiLhs",
        "vpiIndex",
        "vpiLeftRange",
        "vpiLowConn",
        "vpiParent",
        "vpiRhs",
        "vpiRightRange",
        "vpiScope",
        "vpiSysTfCall",
        "vpiTchkDataTerm",
        "vpiTchkNotifier",
        "vpiTchkRefTerm",
        "vpiArgument",
        "vpiBit",
        "vpiDriver",
        "vpiInternalScope",
        "vpiLoad",
        "vpiModDataPathIn",
        "vpiModPathIn",
        "vpiModPathOut",
        "vpiOperand",
        "vpiPortInst",
        "vpiProcess",
        "vpiVariables",
        "vpiUse",
        "vpiExpr",
        "vpiPrimitive",
        "vpiStmt"
    };
    // clang-format on
    if (vpiVal > vpiStmt || vpiVal < vpiCondition) return "*undefined*";
    return names[vpiVal - vpiCondition];
}

const char* strFromVpiCallbackReason(PLI_INT32 vpiVal) {
    // clang-format off
    static const char* const names[] = {
        "*undefined*",
        "cbValueChange",
        "cbStmt",
        "cbForce",
        "cbRelease",
        "cbAtStartOfSimTime",
        "cbReadWriteSynch",
        "cbReadOnlySynch",
        "cbNextSimTime",
        "cbAfterDelay",
        "cbEndOfCompile",
        "cbStartOfSimulation",
        "cbEndOfSimulation",
        "cbError",
        "cbTchkViolation",
        "cbStartOfSave",
        "cbEndOfSave",
        "cbStartOfRestart",
        "cbEndOfRestart",
        "cbStartOfReset",
        "cbEndOfReset",
        "cbEnterInteractive",
        "cbExitInteractive",
        "cbInteractiveScopeChange",
        "cbUnresolvedSystf",
        "cbAssign",
        "cbDeassign",
        "cbDisable",
        "cbPLIError",
        "cbSignal",
        "cbNBASynch",
        "cbAtEndOfSimTime"
    };
    // clang-format on
    if (vpiVal < 0) return names[0];
    return names[(vpiVal <= cbAtEndOfSimTime) ? vpiVal : 0];
}

const char* strFromVpiProp(PLI_INT32 vpiVal) {
    // clang-format off
    static const char* const names[] = {
        "*undefined or other*",
        "vpiType",
        "vpiName",
        "vpiFullName",
        "vpiSize",
        "vpiFile",
        "vpiLineNo",
        "vpiTopModule",
        "vpiCellInstance",
        "vpiDefName",
        "vpiProtected",
        "vpiTimeUnit",
        "vpiTimePrecision",
        "vpiDefNetType",
        "vpiUnconnDrive",
        "vpiDefFile",
        "vpiDefLineNo",
        "vpiScalar",
        "vpiVector",
        "vpiExplicitName",
        "vpiDirection",
        "vpiConnByName",
        "vpiNetType",
        "vpiExplicitScalared",
        "vpiExplicitVectored",
        "vpiExpanded",
        "vpiImplicitDecl",
        "vpiChargeStrength",
        "vpiArray",
        "vpiPortIndex",
        "vpiTermIndex",
        "vpiStrength0",
        "vpiStrength1",
        "vpiPrimType",
        "vpiPolarity",
        "vpiDataPolarity",
        "vpiEdge",
        "vpiPathType",
        "vpiTchkType",
        "vpiOpType",
        "vpiConstType",
        "vpiBlocking",
        "vpiCaseType",
        "vpiFuncType",
        "vpiNetDeclAssign",
        "vpiUserDefn",
        "vpiScheduled",
        "*undefined*",
        "*undefined*",
        "vpiActive",
        "vpiAutomatic",
        "vpiCell",
        "vpiConfig",
        "vpiConstantSelect",
        "vpiDecompile",
        "vpiDefAttribute",
        "vpiDelayType",
        "vpiIteratorType",
        "vpiLibrary",
        "*undefined*",
        "vpiOffset",
        "vpiResolvedNetType",
        "vpiSaveRestartID",
        "vpiSaveRestartLocation",
        "vpiValid",
        "vpiSigned",
        "vpiStop",
        "vpiFinish",
        "vpiReset",
        "vpiSetInteractiveScope",
        "vpiLocalParam",
        "vpiModPathHasIfNone",
        "vpiIndexedPartSelectType",
        "vpiIsMemory",
        "vpiIsProtected"
    };
    // clang-format on
    if (vpiVal == vpiUndefined) return "vpiUndefined";
    return names[(vpiVal <= vpiIsProtected) ? vpiVal : 0];
}
const char* strFromVpiConstType(PLI_INT32 constType) {
    // clang-format off
    static const char* const names[] = {
        "*undefined*",
        "vpiDecConst",
        "vpiRealConst",
        "vpiBinaryConst",
        "vpiOctConst",
        "vpiHexConst",
        "vpiStringConst",
        "vpiIntConst",
        "vpiTimeConst",
    };
    // clang-format on
    if (constType < 0) return names[0];
    return names[(constType <= vpiTimeConst) ? constType : 0];
}
