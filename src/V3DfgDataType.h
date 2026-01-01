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
//
// DFG uses a restriced and simplified type system compared to Ast. Each
// DfgVertex has a type, describing the type of the value it represents.
// The DFG types are represented by an instance of DfgDataType defined below.
//
// The type can be one of
// - Null: The vertex doesn't actually represent a value directly
// - Packed: All bit-vector like types, including all packed construct
//   and binary encoded numbers. Packed types are always 1-dimensional
//   with no sub-type. E.g.: a packed array of N copies of M-wide elements
//   is simply represented as a Packed type of size N*M.
// - Array: An unpacked array of elements with the same type.
//
// Each type has a size:
// - Null: 0, though this is largely irrelevant
// - Packed: number of bits in the packed value (minimum 1)
// - Array: number of elements in the arrray
//
// The indexing of Packed and Array are both zero based and 'descending' in
// the Systemverilog sense (index 0 is the LSB of a Packed, index 0 is at the
// lowest memory address for Array).
//
// All types are 'interned', that is, there can only be one instance of
// DfgDataType which represents that type. This means two DfgDataType are
// equal if and only if they are the same DfgDataType instance.
//
//*************************************************************************

#ifndef VERILATOR_V3DFGDATATYPE_H_
#define VERILATOR_V3DFGDATATYPE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3Global.h"

#include <memory>
#include <unordered_map>

class DfgDataType final {
    enum class Kind : uint8_t {
        Packed,
        Array,
        // Tuple - to model unpacked structs in the future
        Null  // No type (like 'void', but that's a C++ keyword)
    };

    // STATE
    const Kind m_kind;  // The type category
    uint32_t m_size;  // The number of elements in this type
    AstNodeDType* const m_astDtypep;  // Equivalent canonical AstNodeDType
    const DfgDataType* const m_elemDtypep;  // Type of elements - for arrays only
    // Static singleton Null type
    static const DfgDataType* s_nullTypep;
    // Static map from 'width' -> 'interned Packed DfgDataType with that width'
    static std::unordered_map<uint32_t, const DfgDataType*> s_packedTypes;
    // Map from 'elements' -> 'interned Array DfgDataType with that many elements of *this* type'
    mutable std::unordered_map<uint32_t, const DfgDataType*> m_arrayTypes;

    // METHODS
    static AstNodeDType* canonicalPackedDType(uint32_t width) {
        return v3Global.rootp()->typeTablep()->findLogicDType(width, width, VSigning::UNSIGNED);
    }
    static AstNodeDType* canonicalArrayDType(uint32_t size, const DfgDataType& elemType) {
        AstNodeDType* const elemDTypep = elemType.m_astDtypep;
        FileLine* const flp = elemDTypep->fileline();
        AstRange* const rangep = new AstRange{flp, static_cast<int>(size - 1), 0};
        AstNodeDType* const dtypep = new AstUnpackArrayDType{flp, elemDTypep, rangep};
        v3Global.rootp()->typeTablep()->addTypesp(dtypep);
        return dtypep;
    }

    // CONSTRUCTOR - use 'fromAst' instead
    DfgDataType()
        : m_kind{Kind::Null}
        , m_size{0}
        , m_astDtypep{v3Global.rootp()->findVoidDType()}
        , m_elemDtypep{nullptr} {}
    explicit DfgDataType(uint32_t size)
        : m_kind{Kind::Packed}
        , m_size{size}
        , m_astDtypep{canonicalPackedDType(size)}
        , m_elemDtypep{nullptr} {}
    DfgDataType(uint32_t size, const DfgDataType& elemType)
        : m_kind{Kind::Array}
        , m_size{size}
        , m_astDtypep{canonicalArrayDType(size, elemType)}
        , m_elemDtypep{&elemType} {}

    VL_UNCOPYABLE(DfgDataType);
    VL_UNMOVABLE(DfgDataType);
    ~DfgDataType() {
        for (const auto& pair : m_arrayTypes) VL_DO_DANGLING(delete pair.second, pair.second);
    }

public:
    //-----------------------------------------------------------------------
    // Properties

    bool isNull() const { return m_kind == Kind::Null; }
    bool isPacked() const { return m_kind == Kind::Packed; }
    bool isArray() const { return m_kind == Kind::Array; }
    // Size of type (this is 'width' for Ppacked, 'elements' for Array, 0 for Null)
    uint32_t size() const { return m_size; }
    AstNodeDType* astDtypep() const { return m_astDtypep; }

    // Thanks to the interning, equality is identity
    bool operator==(const DfgDataType& that) const { return this == &that; }
    bool operator!=(const DfgDataType& that) const { return this != &that; }

    // Type of elements, for arrays only
    const DfgDataType& elemDtype() const {
        UASSERT(isArray(), "Non-array has no 'elemDType'");
        return *m_elemDtypep;
    }

    //-----------------------------------------------------------------------
    // Static factory and management functions

    // Returns a Packed type of the given width
    static const DfgDataType& packed(uint32_t width) {
        // Find or create the right sized packed type
        const DfgDataType*& entryr = s_packedTypes[width];
        if (!entryr) entryr = new DfgDataType{width};
        return *entryr;
    }

    // Returns an Array type of the given size with the given elements
    static const DfgDataType& array(const DfgDataType& elemType, uint32_t size) {
        UASSERT(elemType.isPacked(), "Cannot create multi-dimensional arrays yet");
        // Find or create the right sized array type with this as elements
        const DfgDataType*& entryr = elemType.m_arrayTypes[size];
        if (!entryr) entryr = new DfgDataType{size, elemType};
        return *entryr;
    }

    // Returns the singleton Null type
    static const DfgDataType& null() {
        if (!s_nullTypep) s_nullTypep = new DfgDataType{};
        return *s_nullTypep;
    }

    // Returns the data type of selecting the range [lo + size - 1 : lo] from this type
    static const DfgDataType& select(const DfgDataType& dtype, uint32_t lo, uint32_t size) {
        switch (dtype.m_kind) {
        case Kind::Packed: {
            UASSERT(lo + size - 1 < dtype.size(), "Out of range");
            return DfgDataType::packed(size);
        }
        case Kind::Array: {
            UASSERT(lo + size - 1 < dtype.size(), "Out of range");
            return DfgDataType::array(dtype.elemDtype(), size);
        }
        case Kind::Null: v3fatal("Type cannot be selected from");  // LCOV_EXCL_LINE
        }
        VL_UNREACHABLE;
    }

    // Construct a DfgDataType that represents the given AstNodeDType.
    // Returns nullptr if AstNodeDType is not representable by DfgDataType.
    static const DfgDataType* fromAst(const AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();

        if (const AstUnpackArrayDType* const typep = VN_CAST(dtypep, UnpackArrayDType)) {
            // Convert the element type
            const DfgDataType* const elemp = fromAst(typep->subDTypep());
            // If element type is not supported, we cannot handle the array either
            if (!elemp) return nullptr;
            // Currently restricted to 1-dimensional arrays, just assumptions in the code
            if (elemp->isArray()) return nullptr;
            // Unpacked array maps to Array
            return &array(*elemp, typep->elementsConst());
        }

        if (const AstPackArrayDType* const typep = VN_CAST(dtypep, PackArrayDType)) {
            // Packed array maps to Packed
            return &packed(typep->width());
        }

        if (const AstStructDType* const typep = VN_CAST(dtypep, StructDType)) {
            // Unpacked structs currently not supported
            if (!typep->packed()) return nullptr;
            // Packed struct maps to Packed
            return &packed(typep->width());
        }

        if (const AstUnionDType* const typep = VN_CAST(dtypep, UnionDType)) {
            // Unpacked unions not supported
            if (!typep->packed()) return nullptr;
            // Packed union maps to Packed
            return &packed(typep->width());
        }

        if (const AstBasicDType* const typep = VN_CAST(dtypep, BasicDType)) {
            // Anything not resembling a binary encoded number is not supported
            if (!typep->keyword().isIntNumeric()) return nullptr;
            // Basic numeric types map to Packed
            return &packed(typep->width());
        }

        // Anything else is not representable
        return nullptr;
    }

    // Reset interned types
    static void reset() {
        for (const auto& pair : s_packedTypes) VL_DO_DANGLING(delete pair.second, pair.second);
        s_packedTypes.clear();
        delete s_nullTypep;
        s_nullTypep = nullptr;
    }
};

#endif
