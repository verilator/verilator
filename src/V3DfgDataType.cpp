// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Type system used by DFG
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//------------------------------------------------------------------------------
// DfgDataType

const DfgDataType* DfgDataType::s_nullTypep{nullptr};
std::unordered_map<uint32_t, const DfgDataType*> DfgDataType::s_packedTypes{};

//------------------------------------------------------------------------------
// Type checker - for internal validation only

void V3DfgPasses::typeCheck(const DfgGraph& dfg) {
    dfg.forEachVertex([&](const DfgVertex& vtx) {
#define CHECK(cond, msg) \
    UASSERT_OBJ(cond, &vtx, \
                "Dfg type error for vertex " << vtx.typeName() << " in " << dfg.name() << ": " \
                                             << msg);
        switch (vtx.type()) {
        case VDfgType::Const: {
            CHECK(vtx.isPacked(), "Should be Packed type");
            return;
        }
        case VDfgType::VarArray:
        case VDfgType::VarPacked: {
            const DfgVertexVar& v = *vtx.as<DfgVertexVar>();
            CHECK(!v.defaultp() || v.defaultp()->dtype() == v.dtype(), "'defaultp' should match");
            CHECK(!v.srcp() || v.srcp()->dtype() == v.dtype(), "'srcp' should match");
            return;
        }
        case VDfgType::SpliceArray:
        case VDfgType::SplicePacked: {
            const DfgVertexSplice& v = *vtx.as<DfgVertexSplice>();
            v.foreachDriver([&](const DfgVertex& src, uint32_t lo) {
                CHECK(src.dtype() == DfgDataType::select(v.dtype(), lo, src.size()), "driver");
                return false;
            });
            return;
        }
        case VDfgType::Logic: {
            CHECK(vtx.dtype().isNull(), "Should be Null type");
            return;
        }
        case VDfgType::Unresolved: {
            CHECK(!vtx.dtype().isNull(), "Should not be Null type");
            return;
        }
        case VDfgType::UnitArray: {
            const DfgUnitArray& v = *vtx.as<DfgUnitArray>();
            CHECK(v.isArray(), "Should be Array type");
            CHECK(v.size() == 1, "Should be one element");
            CHECK(v.srcp()->dtype() == v.dtype().elemDtype(), "Input should be the element type");
            return;
        }
        case VDfgType::Sel: {
            const DfgSel& v = *vtx.as<DfgSel>();
            CHECK(v.isPacked(), "Should be Packed type");
            CHECK(v.dtype() == DfgDataType::select(v.srcp()->dtype(), v.lsb(), v.size()), "sel");
            return;
        }
        case VDfgType::Mux: {
            const DfgMux& v = *vtx.as<DfgMux>();
            CHECK(v.isPacked(), "Should be Packed type");
            CHECK(v.fromp()->isPacked(), "Source operand should be Packed type");
            CHECK(v.fromp()->size() >= v.size(), "Source operand should not be narrower");
            CHECK(v.lsbp()->isPacked(), "Index should be Packed type");
            return;
        }
        case VDfgType::ArraySel: {
            const DfgArraySel& v = *vtx.as<DfgArraySel>();
            CHECK(v.dtype() == v.fromp()->dtype().elemDtype(), "Element type should match");
            CHECK(v.bitp()->isPacked(), "Index should be Packed type");
            return;
        }

        case VDfgType::Add:
        case VDfgType::And:
        case VDfgType::BufIf1:
        case VDfgType::Div:
        case VDfgType::DivS:
        case VDfgType::ModDiv:
        case VDfgType::ModDivS:
        case VDfgType::Mul:
        case VDfgType::MulS:
        case VDfgType::Or:
        case VDfgType::Sub:
        case VDfgType::Xor: {
            CHECK(vtx.isPacked(), "Should be Packed type");
            CHECK(vtx.inputp(0)->dtype() == vtx.dtype(), "LHS should be same type");
            CHECK(vtx.inputp(1)->dtype() == vtx.dtype(), "RHS should be same type");
            return;
        }

        case VDfgType::Negate:
        case VDfgType::Not: {
            CHECK(vtx.isPacked(), "Should be Packed type");
            CHECK(vtx.inputp(0)->dtype() == vtx.dtype(), "Input should be same type");
            return;
        }

        case VDfgType::ShiftL:
        case VDfgType::ShiftR:
        case VDfgType::ShiftRS: {
            CHECK(vtx.isPacked(), "Should be Packed type");
            CHECK(vtx.inputp(0)->dtype() == vtx.dtype(), "LHS should be same type");
            CHECK(vtx.inputp(1)->isPacked(), "RHS should be Packed type");
            return;
        }

        case VDfgType::Concat: {
            const DfgConcat& v = *vtx.as<DfgConcat>();
            CHECK(v.isPacked(), "Should be Packed type");
            CHECK(v.lhsp()->isPacked(), "LHS should be Packed type");
            CHECK(v.rhsp()->isPacked(), "RHS should be Packed type");
            CHECK(v.size() == v.rhsp()->size() + v.lhsp()->size(), "Concat result mismatch");
            return;
        }

        case VDfgType::Replicate: {
            // TODO: model DfgReplicate without an explicit 'countp' which is always constant
            const DfgReplicate& v = *vtx.as<DfgReplicate>();
            CHECK(v.isPacked(), "Should be Packed type");
            CHECK(v.srcp()->isPacked(), "'srcp' should be same type");
            CHECK(v.countp()->isPacked(), "'countp' should be Packed type");
            CHECK(v.size() % v.srcp()->size() == 0, "Not a replicate");
            return;
        }

        case VDfgType::StreamL:
        case VDfgType::StreamR: {
            // TODO: model these without an explicit slice size which is always constant (?)
            CHECK(vtx.isPacked(), "Should be Packed type");
            CHECK(vtx.inputp(0)->dtype() == vtx.dtype(), "LHS should be same type");
            CHECK(vtx.inputp(1)->isPacked(), "Slice size should be Packed type");
            return;
        }

        case VDfgType::Eq:
        case VDfgType::EqCase:
        case VDfgType::EqWild:
        case VDfgType::Neq:
        case VDfgType::NeqCase:
        case VDfgType::NeqWild:
        case VDfgType::Gt:
        case VDfgType::GtS:
        case VDfgType::Gte:
        case VDfgType::GteS:
        case VDfgType::Lt:
        case VDfgType::LtS:
        case VDfgType::Lte:
        case VDfgType::LteS: {
            CHECK(vtx.dtype() == DfgDataType::packed(1), "Should be 1-bit");
            CHECK(vtx.inputp(0)->dtype() == vtx.inputp(1)->dtype(), "Sides should match");
            return;
        }

        case VDfgType::Extend:
        case VDfgType::ExtendS: {
            CHECK(vtx.isPacked(), "Should be Packed type");
            CHECK(vtx.inputp(0)->isPacked(), "Operand should be same type");
            CHECK(vtx.inputp(0)->size() < vtx.size(), "Operand should be narrower");
            return;
        }

        case VDfgType::LogAnd:
        case VDfgType::LogEq:
        case VDfgType::LogIf:
        case VDfgType::LogOr: {
            CHECK(vtx.dtype() == DfgDataType::packed(1), "Should be 1-bit");
            CHECK(vtx.inputp(0)->isPacked(), "LHS should be Packed type");
            CHECK(vtx.inputp(1)->isPacked(), "RHS should be Packed type");
            return;
        }

        case VDfgType::LogNot:
        case VDfgType::RedAnd:
        case VDfgType::RedOr:
        case VDfgType::RedXor: {
            CHECK(vtx.dtype() == DfgDataType::packed(1), "Should be 1-bit");
            CHECK(vtx.inputp(0)->isPacked(), "Operand should be Packed type");
            return;
        }

        case VDfgType::Cond: {
            const DfgCond& v = *vtx.as<DfgCond>();
            CHECK(v.isPacked(), "Should be Packed type");
            CHECK(v.condp()->isPacked(), "Condition should be Packed type");
            CHECK(v.thenp()->dtype() == v.dtype(), "Then should be same type");
            CHECK(v.elsep()->dtype() == v.dtype(), "Else should be same type");
            return;
        }

        case VDfgType::Pow:
        case VDfgType::PowSS:
        case VDfgType::PowSU:
        case VDfgType::PowUS: {
            CHECK(vtx.isPacked(), "Should be Packed type");
            CHECK(vtx.inputp(0)->dtype() == vtx.dtype(), "LHS should be same type");
            CHECK(vtx.inputp(1)->isPacked(), "RHS should be Packed type");
            return;
        }
        }
#undef CHECK
    });
}
