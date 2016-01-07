// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2016 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//=========================================================================
///
/// \file
/// \brief Verilator: VPI implementation code
///
///	This file must be compiled and linked against all objects
///	created from Verilator or called by Verilator that use the VPI.
///
///     Use "verilator --vpi" to add this to the Makefile for the linker.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================


#include "verilated.h"
#include "verilated_vpi.h"

//======================================================================

VerilatedVpi VerilatedVpi::s_s;  // Singleton
vluint8_t* VerilatedVpio::s_freeHead = NULL;

//======================================================================
// VerilatedVpi Methods


VerilatedVpiError* VerilatedVpi::error_info() {
    if (s_s.m_errorInfop == NULL) {
	s_s.m_errorInfop = new VerilatedVpiError();
    }
    return s_s.m_errorInfop;
}

//======================================================================
// VerilatedVpiError Methods

const char* VerilatedVpiError::strFromVpiVal(PLI_INT32 vpiVal) {
    static const char *names[] = {
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
    if (vpiVal < 0) return names[0];
    return names[(vpiVal<=vpiRawFourStateVal)?vpiVal:0];
}
const char* VerilatedVpiError::strFromVpiObjType(PLI_INT32 vpiVal) {
    static const char *names[] = {
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
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
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
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "vpiContAssignBit",
        "vpiNamedEventArray",
        "vpiIndexedPartSelect",
        "*undefined*",
        "*undefined*",
        "vpiGenScopeArray",
        "vpiGenScope",
        "vpiGenVar"
    };
    if (vpiVal < 0) return names[0];
    return names[(vpiVal<=vpiGenVar)?vpiVal:0];
}
const char* VerilatedVpiError::strFromVpiMethod(PLI_INT32 vpiVal) {
    static const char *names[] = {
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
    if (vpiVal>vpiStmt || vpiVal<vpiCondition) {
        return "*undefined*";
    }
    return names[vpiVal-vpiCondition];
}

const char* VerilatedVpiError::strFromVpiCallbackReason(PLI_INT32 vpiVal) {
    static const char *names[] = {
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
    if (vpiVal < 0) return names[0];
    return names[(vpiVal<=cbAtEndOfSimTime)?vpiVal:0];
}

const char* VerilatedVpiError::strFromVpiProp(PLI_INT32 vpiVal) {
    static const char *names[] = {
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
    if (vpiVal == vpiUndefined) {
      return "vpiUndefined";
    }
    return names[(vpiVal<=vpiIsProtected)?vpiVal:0];
}

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got),(exp))) { \
        string msg = string("%Error: ") \
             + "GOT = '"+((got)?(got):"<null>")+"'" \
             + "  EXP = '"+((exp)?(exp):"<null>")+"'"; \
        vl_fatal(__FILE__,__LINE__,"",msg.c_str()); \
    }

#define CHECK_ENUM_STR(fn, enum) \
    do { \
        const char* strVal = VerilatedVpiError::fn(enum);	\
        CHECK_RESULT_CSTR(strVal, #enum); \
    } while (0)

void VerilatedVpiError::selfTest() {
    CHECK_ENUM_STR(strFromVpiVal, vpiBinStrVal);
    CHECK_ENUM_STR(strFromVpiVal, vpiRawFourStateVal);

    CHECK_ENUM_STR(strFromVpiObjType, vpiAlways);
    CHECK_ENUM_STR(strFromVpiObjType, vpiWhile);
    CHECK_ENUM_STR(strFromVpiObjType, vpiAttribute);
    CHECK_ENUM_STR(strFromVpiObjType, vpiUdpArray);
    CHECK_ENUM_STR(strFromVpiObjType, vpiContAssignBit);
    CHECK_ENUM_STR(strFromVpiObjType, vpiGenVar);

    CHECK_ENUM_STR(strFromVpiMethod, vpiCondition);
    CHECK_ENUM_STR(strFromVpiMethod, vpiStmt);

    CHECK_ENUM_STR(strFromVpiCallbackReason, cbValueChange);
    CHECK_ENUM_STR(strFromVpiCallbackReason, cbAtEndOfSimTime);

    CHECK_ENUM_STR(strFromVpiProp, vpiType);
    CHECK_ENUM_STR(strFromVpiProp, vpiProtected);
    CHECK_ENUM_STR(strFromVpiProp, vpiDirection);
    CHECK_ENUM_STR(strFromVpiProp, vpiTermIndex);
    CHECK_ENUM_STR(strFromVpiProp, vpiConstType);
    CHECK_ENUM_STR(strFromVpiProp, vpiAutomatic);
    CHECK_ENUM_STR(strFromVpiProp, vpiOffset);
    CHECK_ENUM_STR(strFromVpiProp, vpiStop);
    CHECK_ENUM_STR(strFromVpiProp, vpiIsProtected);
}

#undef CHECK_ENUM_STR
#undef CHECK_RESULT_CSTR

//======================================================================
// callback related

vpiHandle vpi_register_cb(p_cb_data cb_data_p) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!cb_data_p)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s : callback data pointer is null", VL_FUNC);
        return NULL;
    }
    switch (cb_data_p->reason) {
    case cbAfterDelay: {
	QData time = 0;
	if (cb_data_p->time) time = _VL_SET_QII(cb_data_p->time->high, cb_data_p->time->low);
	VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, VL_TIME_Q()+time);
	VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_register_cb %d %p delay=%" VL_PRI64 "u\n",cb_data_p->reason,vop,time););
	VerilatedVpi::cbTimedAdd(vop);
	return vop->castVpiHandle();
    }
    case cbReadWriteSynch:		// FALLTHRU // Supported via vlt_main.cpp
    case cbReadOnlySynch:		// FALLTHRU // Supported via vlt_main.cpp
    case cbNextSimTime:			// FALLTHRU // Supported via vlt_main.cpp
    case cbStartOfSimulation:		// FALLTHRU // Supported via vlt_main.cpp
    case cbEndOfSimulation:		// FALLTHRU // Supported via vlt_main.cpp
    case cbValueChange:			// FALLTHRU // Supported via vlt_main.cpp
    case cbPLIError:			// FALLTHRU // NOP, but need to return handle, so make object
    case cbEnterInteractive:		// FALLTHRU // NOP, but need to return handle, so make object
    case cbExitInteractive:		// FALLTHRU // NOP, but need to return handle, so make object
    case cbInteractiveScopeChange: {	// FALLTHRU // NOP, but need to return handle, so make object
	VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, 0);
	VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_register_cb %d %p\n",cb_data_p->reason,vop););
	VerilatedVpi::cbReasonAdd(vop);
	return vop->castVpiHandle();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported callback type %s",
			VL_FUNC, VerilatedVpiError::strFromVpiCallbackReason(cb_data_p->reason));
	return NULL;
    };
}

PLI_INT32 vpi_remove_cb(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_remove_cb %p\n",object););
    VerilatedVpioCb* vop = VerilatedVpioCb::castp(object);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!vop)) return 0;
    if (vop->cb_datap()->reason == cbAfterDelay) {
	VerilatedVpi::cbTimedRemove(vop);
    } else {
	VerilatedVpi::cbReasonRemove(vop);
    }
    return 1;
}

void vpi_get_cb_info(vpiHandle object, p_cb_data cb_data_p) {
    _VL_VPI_UNIMP(); return;
}
vpiHandle vpi_register_systf(p_vpi_systf_data systf_data_p) {
    _VL_VPI_UNIMP(); return 0;
}
void vpi_get_systf_info(vpiHandle object, p_vpi_systf_data systf_data_p) {
    _VL_VPI_UNIMP(); return;
}

// for obtaining handles

vpiHandle vpi_handle_by_name(PLI_BYTE8* namep, vpiHandle scope) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!namep)) return NULL;
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_handle_by_name %s %p\n",namep,scope););
    VerilatedVpioScope* voScopep = VerilatedVpioScope::castp(scope);
    const VerilatedVar* varp;
    const VerilatedScope* scopep;
    string scopeAndName = namep;
    if (voScopep) {
	scopeAndName = string(voScopep->fullname()) + "." + namep;
	namep = (PLI_BYTE8*)scopeAndName.c_str();
    }
    {
	// This doesn't yet follow the hierarchy in the proper way
	scopep = Verilated::scopeFind(namep);
	if (scopep) {  // Whole thing found as a scope
	    return (new VerilatedVpioScope(scopep))->castVpiHandle();
	}
	const char* baseNamep = scopeAndName.c_str();
	string scopename;
	const char* dotp = strrchr(namep, '.');
	if (VL_LIKELY(dotp)) {
	    baseNamep = dotp+1;
	    scopename = string(namep,dotp-namep);
	}
	scopep = Verilated::scopeFind(scopename.c_str());
	if (!scopep) return NULL;
	varp = scopep->varFind(baseNamep);
    }
    if (!varp) return NULL;
    return (new VerilatedVpioVar(varp, scopep))->castVpiHandle();
}

vpiHandle vpi_handle_by_index(vpiHandle object, PLI_INT32 indx) {
    // Used to get array entries
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_handle_by_index %p %d\n",object, indx););
    VerilatedVpioVar* varop = VerilatedVpioVar::castp(object);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_LIKELY(varop)) {
	if (varop->varp()->dims()<2) return 0;
	if (VL_LIKELY(varop->varp()->array().left() >= varop->varp()->array().right())) {
	    if (VL_UNLIKELY(indx > varop->varp()->array().left() || indx < varop->varp()->array().right())) return 0;
	    return (new VerilatedVpioMemoryWord(varop->varp(), varop->scopep(), indx,
					      indx - varop->varp()->array().right()))
		->castVpiHandle();
	} else {
	    if (VL_UNLIKELY(indx < varop->varp()->array().left() || indx > varop->varp()->array().right())) return 0;
	    return (new VerilatedVpioMemoryWord(varop->varp(), varop->scopep(), indx,
					      indx - varop->varp()->array().left()))
		->castVpiHandle();
	}
    } else {
	_VL_VPI_INTERNAL(__FILE__, __LINE__, "%s : can't resolve handle", VL_FUNC);
        return 0;
    }
}

// for traversing relationships

vpiHandle vpi_handle(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_handle %d %p\n",type,object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    switch (type) {
    case vpiLeftRange: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	if (VL_UNLIKELY(!vop->rangep())) return 0;
        return (new VerilatedVpioConst(vop->rangep()->left()))->castVpiHandle();
    }
    case vpiRightRange: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	if (VL_UNLIKELY(!vop->rangep())) return 0;
        return (new VerilatedVpioConst(vop->rangep()->right()))->castVpiHandle();
    }
    case vpiIndex: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
        return (new VerilatedVpioConst(vop->index()))->castVpiHandle();
    }
    case vpiScope: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return (new VerilatedVpioScope(vop->scopep()))->castVpiHandle();
    }
    case vpiParent: {
	VerilatedVpioMemoryWord* vop = VerilatedVpioMemoryWord::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return (new VerilatedVpioVar(vop->varp(), vop->scopep()))->castVpiHandle();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
			VL_FUNC, VerilatedVpiError::strFromVpiMethod(type));
	return 0;
    }
}

vpiHandle vpi_handle_multi(PLI_INT32 type, vpiHandle refHandle1, vpiHandle refHandle2, ... ) {
    _VL_VPI_UNIMP(); return 0;
}

vpiHandle vpi_iterate(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_iterate %d %p\n",type,object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    switch (type) {
    case vpiMemoryWord: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	if (vop->varp()->dims() < 2) return 0;
	if (vop->varp()->dims() > 2) {
	    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: %s, object %s has unsupported number of indices (%d)",
			    VL_FUNC, VerilatedVpiError::strFromVpiMethod(type), vop->fullname() , vop->varp()->dims());
	}
	return (new VerilatedVpioMemoryWordIter(object, vop->varp()))->castVpiHandle();
    }
    case vpiRange: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	if (vop->varp()->dims() < 2) return 0;
	// Unsupported is multidim list
        if (vop->varp()->dims() > 2) {
	    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: %s, object %s has unsupported number of indices (%d)",
			    VL_FUNC, VerilatedVpiError::strFromVpiMethod(type), vop->fullname() , vop->varp()->dims());
	}
	return ((new VerilatedVpioRange(vop->rangep()))->castVpiHandle());
    }
    case vpiReg: {
	VerilatedVpioScope* vop = VerilatedVpioScope::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return ((new VerilatedVpioVarIter(vop->scopep()))
		->castVpiHandle());
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
			VL_FUNC, VerilatedVpiError::strFromVpiObjType(type));
	return 0;
    }
}
vpiHandle vpi_scan(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_scan %p\n",object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    if (VL_UNLIKELY(!vop)) return NULL;
    return vop->dovpi_scan();
}

// for processing properties

PLI_INT32 vpi_get(PLI_INT32 property, vpiHandle object) {
    // Leave this in the header file - in many cases the compiler can constant propagate "object"
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get %d %p\n",property,object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    switch (property) {
    case vpiTimePrecision: {
	return VL_TIME_PRECISION;
    }
    case vpiType: {
	VerilatedVpio* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return vop->type();
    }
    case vpiDirection: {
	// By forthought, the directions already are vpi enumerated
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return vop->varp()->vldir();
    }
    case vpiScalar:  // FALLTHRU
    case vpiVector: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
        return (property==vpiVector)^(vop->varp()->dims()==0);
    }
    case vpiSize: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return vop->size();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
			VL_FUNC, VerilatedVpiError::strFromVpiProp(property));
	return 0;
    }
}

PLI_INT64 vpi_get64(PLI_INT32 property, vpiHandle object) {
    _VL_VPI_UNIMP();
    return 0;
}

PLI_BYTE8 *vpi_get_str(PLI_INT32 property, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get_str %d %p\n",property,object););
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!vop)) return NULL;
    switch (property) {
    case vpiName: {
	return (PLI_BYTE8*)vop->name();
    }
    case vpiFullName: {
	return (PLI_BYTE8*)vop->fullname();
    }
    case vpiDefName: {
	return (PLI_BYTE8*)vop->defname();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
			VL_FUNC, VerilatedVpiError::strFromVpiProp(property));
	return 0;
    }
}

// delay processing

void vpi_get_delays(vpiHandle object, p_vpi_delay delay_p) {
    _VL_VPI_UNIMP();
    return;
}
void vpi_put_delays(vpiHandle object, p_vpi_delay delay_p) {
    _VL_VPI_UNIMP();
    return;
}

// value processing

void vpi_get_value(vpiHandle object, p_vpi_value value_p) {
    static VL_THREAD char outStr[1+VL_MULS_MAX_WORDS*32]; // Maximum required size is for binary string, one byte per bit plus null termination
    // cppcheck-suppress variableScope
    static VL_THREAD int outStrSz = sizeof(outStr)-1;
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get_value %p\n",object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!value_p)) return;
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
	// We used to presume vpiValue.format = vpiIntVal or if single bit vpiScalarVal
        // This may cause backward compatability issues with older code.
	if (value_p->format == vpiVectorVal) {
	    // Vector pointer must come from our memory pool
	    // It only needs to persist until the next vpi_get_value
	    static VL_THREAD t_vpi_vecval out[VL_MULS_MAX_WORDS*2];
	    value_p->value.vector = out;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		out[0].aval = *((CData*)(vop->varDatap()));
		out[0].bval = 0;
		return;
	    case VLVT_UINT16:
		out[0].aval = *((SData*)(vop->varDatap()));
		out[0].bval = 0;
		return;
	    case VLVT_UINT32:
		out[0].aval = *((IData*)(vop->varDatap()));
		out[0].bval = 0;
		return;
	    case VLVT_WDATA: {
		int words = VL_WORDS_I(vop->varp()->range().elements());
		if (VL_UNLIKELY(words >= VL_MULS_MAX_WORDS)) {
		    vl_fatal(__FILE__,__LINE__,"", "vpi_get_value with more than VL_MULS_MAX_WORDS; increase and recompile");
		}
		WDataInP datap = ((IData*)(vop->varDatap()));
		for (int i=0; i<words; i++) {
		    out[i].aval = datap[i];
		    out[i].bval = 0;
		}
		return;
	    }
	    case VLVT_UINT64: {
		QData data = *((QData*)(vop->varDatap()));
		out[1].aval = (IData)(data>>VL_ULL(32));
		out[1].bval = 0;
		out[0].aval = (IData)(data);
		out[0].bval = 0;
		return;
	    }
	    default: {
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	    }
	} else if (value_p->format == vpiBinStrVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int bits = vop->varp()->range().elements();
		CData* datap = ((CData*)(vop->varDatap()));
		int i;
		if (bits > outStrSz) {
		  // limit maximum size of output to size of buffer to prevent overrun.
		  bits = outStrSz;
		  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
				  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, bits);
		}
		for (i=0; i<bits; i++) {
		    char val = (datap[i>>3]>>(i&7))&1;
		    outStr[bits-i-1] = val?'1':'0';
		}
		outStr[i]=0; // NULL terminate
		return;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiOctStrVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int chars = (vop->varp()->range().elements()+2)/3;
		int bytes = VL_BYTES_I(vop->varp()->range().elements());
		CData* datap = ((CData*)(vop->varDatap()));
		int i;
		if (chars > outStrSz) {
		    // limit maximum size of output to size of buffer to prevent overrun.
		    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
				    VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, chars);
		    chars = outStrSz;
	        }
		for (i=0; i<chars; i++) {
                    div_t idx = div(i*3, 8);
		    int val = datap[idx.quot];
                    if ((idx.quot+1)<bytes) {
			// if the next byte is valid or that in
                        // for when the required 3 bits straddle adjacent bytes
                        val |= datap[idx.quot+1]<<8;
		    }
                    // align so least significant 3 bits represent octal char
		    val >>= idx.rem;
                    if (i==(chars-1)) {
			// most signifcant char, mask off non existant bits when vector
                        // size is not a multiple of 3
			unsigned int rem = vop->varp()->range().elements() % 3;
                        if (rem) {
			    // generate bit mask & zero non existant bits
                            val &= (1<<rem)-1;
			}
		    }
		    outStr[chars-i-1] = '0' + (val&7);
		}
		outStr[i]=0; // NULL terminate
		return;
	    }
	    default:
                strcpy(outStr, "0");
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiDecStrVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    // outStrSz does not include NULL termination so add one
	    case VLVT_UINT8 : VL_SNPRINTF(outStr, outStrSz+1, "%hhu", (unsigned char )*((CData*)(vop->varDatap()))); return;
	    case VLVT_UINT16: VL_SNPRINTF(outStr, outStrSz+1, "%hu",  (unsigned short)*((SData*)(vop->varDatap()))); return;
	    case VLVT_UINT32: VL_SNPRINTF(outStr, outStrSz+1, "%u",   (unsigned int  )*((IData*)(vop->varDatap()))); return;
	    case VLVT_UINT64: VL_SNPRINTF(outStr, outStrSz+1, "%llu",  (unsigned long long)*((QData*)(vop->varDatap()))); return;
	    default:
                strcpy(outStr, "-1");
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s, maximum limit is 64 bits",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiHexStrVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int chars = (vop->varp()->range().elements()+3)>>2;
		CData* datap = ((CData*)(vop->varDatap()));
		int i;
		if (chars > outStrSz) {
		  // limit maximum size of output to size of buffer to prevent overrun.
		  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
				  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, chars);
		  chars = outStrSz;
		}
		for (i=0; i<chars; i++) {
		    char val = (datap[i>>1]>>((i&1)<<2))&15;
                    static char hex[] = "0123456789abcdef";
                    if (i==(chars-1)) {
			// most signifcant char, mask off non existant bits when vector
                        // size is not a multiple of 4
			unsigned int rem = vop->varp()->range().elements() & 3;
                        if (rem) {
			    // generate bit mask & zero non existant bits
                            val &= (1<<rem)-1;
			}
		    }
		    outStr[chars-i-1] = hex[static_cast<int>(val)];
		}
		outStr[i]=0; // NULL terminate
		return;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiStringVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int bytes = VL_BYTES_I(vop->varp()->range().elements());
		CData* datap = ((CData*)(vop->varDatap()));
		int i;
		if (bytes > outStrSz) {
		  // limit maximum size of output to size of buffer to prevent overrun.
		  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
				  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
				  vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, bytes);
		  bytes = outStrSz;
		}
		for (i=0; i<bytes; i++) {
		    char val = datap[bytes-i-1];
                     // other simulators replace [leading?] zero chars with spaces, replicate here.
		    outStr[i] = val?val:' ';
		}
		outStr[i]=0; // NULL terminate
		return;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiIntVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		value_p->value.integer = *((CData*)(vop->varDatap()));
		return;
	    case VLVT_UINT16:
		value_p->value.integer = *((SData*)(vop->varDatap()));
		return;
	    case VLVT_UINT32:
		value_p->value.integer = *((IData*)(vop->varDatap()));
		return;
	    case VLVT_WDATA:
	    case VLVT_UINT64:
		// Not legal
		value_p->value.integer = 0;
	    default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiSuppressVal) {
	    return;
	}
        _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) as requested for %s",
		      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
	return;
    }
    else if (VerilatedVpioConst* vop = VerilatedVpioConst::castp(object)) {
	if (value_p->format == vpiIntVal) {
	  value_p->value.integer = vop->num();
	  return;
	}
        _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
		      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
        return;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format %s",
		  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format));
}

vpiHandle vpi_put_value(vpiHandle object, p_vpi_value value_p,
			p_vpi_time time_p, PLI_INT32 flags) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_put_value %p %p\n",object, value_p););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!value_p)) {
      _VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_put_value with NULL value pointer");
      return 0;
    }
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
	VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:    vpi_put_value name=%s fmt=%d vali=%d\n",
				  vop->fullname(), value_p->format, value_p->value.integer);
			VL_PRINTF("-vltVpi:    varp=%p  putatp=%p\n",
				  vop->varp()->datap(), vop->varDatap()););
	if (VL_UNLIKELY(!vop->varp()->isPublicRW())) {
            _VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_put_value to signal marked read-only, use public_flat_rw instead: ", vop->fullname());
	    return 0;
	}
	if (value_p->format == vpiVectorVal) {
	    if (VL_UNLIKELY(!value_p->value.vector)) return NULL;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		*((CData*)(vop->varDatap())) = value_p->value.vector[0].aval & vop->mask();
		return object;
	    case VLVT_UINT16:
		*((SData*)(vop->varDatap())) = value_p->value.vector[0].aval & vop->mask();
		return object;
	    case VLVT_UINT32:
		*((IData*)(vop->varDatap())) = value_p->value.vector[0].aval & vop->mask();
		return object;
	    case VLVT_WDATA: {
		int words = VL_WORDS_I(vop->varp()->range().elements());
		WDataOutP datap = ((IData*)(vop->varDatap()));
		for (int i=0; i<words; i++) {
		    datap[i] = value_p->value.vector[i].aval;
                    if (i==(words-1)) {
			datap[i] &= vop->mask();
		    }
		}
		return object;
	    }
	    case VLVT_UINT64: {
		*((QData*)(vop->varDatap())) = _VL_SET_QII(
		    value_p->value.vector[1].aval & vop->mask(),
		    value_p->value.vector[0].aval);
		return object;
	    }
	    default: {
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return NULL;
	    }
	    }
	} else if (value_p->format == vpiBinStrVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int bits = vop->varp()->range().elements();
		int len	 = strlen(value_p->value.str);
		CData* datap = ((CData*)(vop->varDatap()));
		for (int i=0; i<bits; i++) {
                    char set = (i < len)?(value_p->value.str[len-i-1]=='1'):0;
                    // zero bits 7:1 of byte when assigning to bit 0, else
                    // or in 1 if bit set
		    if (i&7) {
		        datap[i>>3] |= set<<(i&7);
		    } else {
		        datap[i>>3]  = set;
		    }
		}
		return object;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	} else if (value_p->format == vpiOctStrVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int chars = (vop->varp()->range().elements()+2)/3;
		int bytes = VL_BYTES_I(vop->varp()->range().elements());
		int len	 = strlen(value_p->value.str);
		CData* datap = ((CData*)(vop->varDatap()));
                div_t idx;
                datap[0] = 0; // reset zero'th byte
		for (int i=0; i<chars; i++) {
                    union {
			char  byte[2];
                        short half;
		    } val;
                    idx = div(i*3, 8);
                    if (i < len) {
			// ignore illegal chars
                        char digit = value_p->value.str[len-i-1];
                        if (digit >= '0' && digit <= '7') {
                            val.half = digit-'0';
			} else {
			    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Non octal character '%c' in '%s' as value %s for %s",
					    VL_FUNC, digit, value_p->value.str,
					    VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
                            val.half = 0;
			}
		    } else {
                        val.half = 0;
		    }
                    // align octal character to position within vector, note that
                    // the three bits may straddle a byte bounday so two byte wide
                    // assignments are made to adjacent bytes - but not if the least
                    // signifcant byte of the aligned value is the most significant
                    // byte of the destination.
                    val.half <<= idx.rem;
                    datap[idx.quot] |= val.byte[0]; // or in value
                    if ((idx.quot+1) < bytes) {
		        datap[idx.quot+1] = val.byte[1]; // this also resets all bits to 0 prior to or'ing above
		    }
		}
                // mask off non existant bits in the most significant byte
                if (idx.quot == (bytes-1)) {
                    datap[idx.quot] &= vop->mask_byte(idx.quot);
		} else if (idx.quot+1 == (bytes-1)) {
                    datap[idx.quot+1] &= vop->mask_byte(idx.quot+1);
		}
                // zero off remaining top bytes
                for (int i=idx.quot+2; i<bytes; i++) {
		    datap[i] = 0;
		}
		return object;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	} else if (value_p->format == vpiDecStrVal) {
            char remainder[16];
            unsigned long long val;
            int success = sscanf(value_p->value.str, "%30llu%15s", &val, remainder);
            if (success < 1) {
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Parsing failed for '%s' as value %s for %s",
			      VL_FUNC, value_p->value.str, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
                return 0;
	    }
            if (success > 1) {
		_VL_VPI_WARNING(__FILE__, __LINE__, "%s: Trailing garbage '%s' in '%s' as value %s for %s",
				VL_FUNC, remainder, value_p->value.str, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
	    }
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 : *((CData*)(vop->varDatap())) = val & vop->mask(); break;
	    case VLVT_UINT16: *((SData*)(vop->varDatap())) = val & vop->mask(); break;
	    case VLVT_UINT32: *((IData*)(vop->varDatap())) = val & vop->mask(); break;
	    case VLVT_UINT64: *((QData*)(vop->varDatap())) = val; ((IData*)(vop->varDatap()))[1] &= vop->mask(); break;
	    case VLVT_WDATA:
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s, maximum limit is 64 bits",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
            return object;
	} else if (value_p->format == vpiHexStrVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int chars = (vop->varp()->range().elements()+3)>>2;
		CData* datap = ((CData*)(vop->varDatap()));
                char* val = value_p->value.str;
                // skip hex ident if one is detected at the start of the string
                if (val[0] == '0' && (val[1] == 'x' || val[1] == 'X')) {
		    val += 2;
		}
		int len = strlen(val);
		for (int i=0; i<chars; i++) {
                    char hex;
                    // compute hex digit value
                    if (i < len) {
                        char digit = val[len-i-1];
                        if (digit >= '0' && digit <= '9') hex = digit - '0';
                        else if (digit >= 'a' && digit <= 'f') hex = digit - 'a' + 10;
                        else if (digit >= 'A' && digit <= 'F') hex = digit - 'A' + 10;
                        else {
			     _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Non hex character '%c' in '%s' as value %s for %s",
					     VL_FUNC, digit, value_p->value.str, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
			    hex = 0;
			}
		    } else {
			hex = 0;
		    }
                    // assign hex digit value to destination
		    if (i&1) {
		        datap[i>>1] |= hex<<4;
		    } else {
		        datap[i>>1]  = hex; // this also resets all bits to 0 prior to or'ing above of the msb
		    }
		}
                // apply bit mask to most significant byte
                datap[(chars-1)>>1] &= vop->mask_byte((chars-1)>>1);
		return object;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	} else if (value_p->format == vpiStringVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int bytes = VL_BYTES_I(vop->varp()->range().elements());
		int len	  = strlen(value_p->value.str);
		CData* datap = ((CData*)(vop->varDatap()));
		for (int i=0; i<bytes; i++) {
		    datap[i] = (i < len)?value_p->value.str[len-i-1]:0; // prepend with 0 values before placing string the least signifcant bytes
		}
		return object;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	} else if (value_p->format == vpiIntVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		*((CData*)(vop->varDatap())) = vop->mask() & value_p->value.integer;
		return object;
	    case VLVT_UINT16:
		*((SData*)(vop->varDatap())) = vop->mask() & value_p->value.integer;
		return object;
	    case VLVT_UINT32:
		*((IData*)(vop->varDatap())) = vop->mask() & value_p->value.integer;
		return object;
	    case VLVT_WDATA: // FALLTHRU
	    case VLVT_UINT64: // FALLTHRU
	    default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	}
        _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) as requested for %s",
		      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
	return NULL;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for ??",
		  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format));
    return NULL;
}

void vpi_get_value_array(vpiHandle object, p_vpi_arrayvalue arrayvalue_p,
				       PLI_INT32 *index_p, PLI_UINT32 num) {
    _VL_VPI_UNIMP(); return;
}
void vpi_put_value_array(vpiHandle object, p_vpi_arrayvalue arrayvalue_p,
				       PLI_INT32 *index_p, PLI_UINT32 num) {
    _VL_VPI_UNIMP(); return;
}


// time processing

void vpi_get_time(vpiHandle object, p_vpi_time time_p) {
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!time_p)) {
	_VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_get_time with NULL value pointer");
	return;
    }
    if (time_p->type == vpiSimTime) {
	QData qtime = VL_TIME_Q();
	IData itime[2];
	VL_SET_WQ(itime, qtime);
	time_p->low = itime[0];
	time_p->high = itime[1];
	return;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported type (%d)",
		  VL_FUNC, time_p->type);
    return;
}

// I/O routines

PLI_UINT32 vpi_mcd_open(PLI_BYTE8 *filenamep) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    return VL_FOPEN_S(filenamep,"wb");
}

PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    VL_FCLOSE_I(mcd); return 0;
}

PLI_BYTE8 *vpi_mcd_name(PLI_UINT32 mcd) {
    _VL_VPI_UNIMP(); return 0;
}

PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8 *formatp, ...) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    va_list ap;
    va_start(ap,formatp);
    int chars = vpi_mcd_vprintf(mcd, formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_printf(PLI_BYTE8 *formatp, ...) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    va_list ap;
    va_start(ap,formatp);
    int chars = vpi_vprintf(formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_vprintf(PLI_BYTE8* formatp, va_list ap) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    return VL_VPRINTF(formatp, ap);
}

PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8 *format, va_list ap) {
    FILE* fp = VL_CVT_I_FP(mcd);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!fp)) return 0;
    int chars = vfprintf(fp, format, ap);
    return chars;
}

PLI_INT32 vpi_flush(void) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    Verilated::flushCall();
    return 0;
}

PLI_INT32 vpi_mcd_flush(PLI_UINT32 mcd) {
    FILE* fp = VL_CVT_I_FP(mcd);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!fp)) return 1;
    fflush(fp);
    return 0;
}

// utility routines

PLI_INT32 vpi_compare_objects(vpiHandle object1, vpiHandle object2) {
    _VL_VPI_UNIMP(); return 0;
}
PLI_INT32 vpi_chk_error(p_vpi_error_info error_info_p) {
    // executing vpi_chk_error does not reset error
    // error_info_p can be NULL, so only return level in that case
    p_vpi_error_info _error_info_p = VerilatedVpi::error_info()->getError();
    if (error_info_p && _error_info_p) {
      *error_info_p = *_error_info_p;
    }
    if (!_error_info_p) return 0; // no error occured
    return _error_info_p->level;  // return error severity level
};

PLI_INT32 vpi_free_object(vpiHandle object) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    return vpi_release_handle(object);  // Deprecated
}

PLI_INT32 vpi_release_handle (vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_release_handle %p\n",object););
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!vop)) return 0;
    vpi_remove_cb(object);  // May not be a callback, but that's ok
    delete vop;
    return 1;
}

PLI_INT32 vpi_get_vlog_info(p_vpi_vlog_info vlog_info_p) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    vlog_info_p->argc = Verilated::getCommandArgs()->argc;
    vlog_info_p->argv = (PLI_BYTE8**)Verilated::getCommandArgs()->argv;
    vlog_info_p->product = (PLI_BYTE8*)Verilated::productName();
    vlog_info_p->version = (PLI_BYTE8*)Verilated::productVersion();
    return 1;
}

// routines added with 1364-2001

PLI_INT32 vpi_get_data(PLI_INT32 id, PLI_BYTE8 *dataLoc, PLI_INT32 numOfBytes) {
    _VL_VPI_UNIMP(); return 0;
}
PLI_INT32 vpi_put_data(PLI_INT32 id, PLI_BYTE8 *dataLoc, PLI_INT32 numOfBytes) {
    _VL_VPI_UNIMP(); return 0;
}
void *vpi_get_userdata(vpiHandle obj) {
    _VL_VPI_UNIMP(); return 0;
}
PLI_INT32 vpi_put_userdata(vpiHandle obj, void *userdata) {
    _VL_VPI_UNIMP(); return 0;
}

PLI_INT32 vpi_control(PLI_INT32 operation, ...) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_control %d\n",operation););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    switch (operation) {
    case vpiFinish: {
	vl_finish(__FILE__,__LINE__,"*VPI*");
	return 1;
    }
    case vpiStop: {
	vl_stop(__FILE__,__LINE__,"*VPI*");
	return 1;
    }
    }
    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, ignoring",
		    VL_FUNC, VerilatedVpiError::strFromVpiProp(operation));
    return 0;
}

vpiHandle vpi_handle_by_multi_index(vpiHandle obj, PLI_INT32 num_index, PLI_INT32 *index_array) {
    _VL_VPI_UNIMP(); return 0;
}
