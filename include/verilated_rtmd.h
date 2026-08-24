// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
//
// Verilated run time model descriptor (RTMD) types
//
// Types of the tables that describe a Verilated model's state as data.
// Included by the generated descriptor tables and by verilated_trace.h.
//
// This file is not part of the Verilated public-facing API.
// It is only for internal use.
//
//=============================================================================

#ifndef VERILATOR_VERILATED_RTMD_H_
#define VERILATOR_VERILATED_RTMD_H_

#include "verilated.h"

#include <map>
#include <set>
#include <vector>

class VlRtmdActSetRow;
class VlRtmdDataTypeRow;
class VlRtmdGlobalSymRow;
class VlRtmdSignalTypeRow;
class VlRtmdHierRow;

class VlRtmdActSet;
class VlRtmdDataType;
class VlRtmdSignalType;

//=============================================================================
// Registration structure - one per VerilatedModel

class VlRtmd final {
public:
    // Index of what is not present
    static constexpr uint32_t NOIDX = ~0U;
    // Location of a signal whose value is not accessible
    static constexpr size_t NOADDR = ~static_cast<size_t>(0);

    const VerilatedModel* m_modelp;  // The model *instance* this belongs to
    const void* m_symsp = nullptr;  // Model symbol table base pointer
    const CData* m_activityFlagsp = nullptr;  // Pointer to activity flags array
    struct {  // The options the model was Verilated with
        bool m_trace = false;  // --trace
        bool m_traceParallel = false;  // Dump VCD in parallel (--threads, or hierarchical)
        bool m_traceStructs = false;  // --trace-structs
        bool m_traceUnderscore = false;  // --trace-underscore
        uint32_t m_traceMaxArray = 0;  // --trace-max-array, 0 if no limit
        uint32_t m_traceMaxWidth = 0;  // --trace-max-width, 0 if no limit
    } m_opt;
    // RTMD Tables. All but the activity set table are split into chunks of 2^m_chunkShift rows,
    // and are tables of the chunks, see 'row'.
    const VlRtmdActSetRow* m_actSetsTabp = nullptr;  // Activity set table
    const VlRtmdDataTypeRow* const* m_dataTypesTabpp = nullptr;  // Data type table
    const VlRtmdGlobalSymRow* const* m_globalSymsTabpp = nullptr;  // Global symbols table
    const VlRtmdSignalTypeRow* const* m_signalTypesTabpp = nullptr;  // Signal type table
    const VlRtmdHierRow* const* m_hierTabpp = nullptr;  // Hierarchy table
    uint32_t m_chunkShift = 0;  // Log2 of the rows per chunk of the tables split into chunks

private:
    // Returns the row 'index' of the table 'tabpp' split into chunks
    template <typename T_Row>
    const T_Row& row(const T_Row* const* tabpp, uint32_t index) const {
        // 64 bit, as a chunk can hold 2^32 rows
        const uint64_t index64 = index;
        return tabpp[index64 >> m_chunkShift][index64 & ((uint64_t{1} << m_chunkShift) - 1)];
    }

public:
    // Returns the row 'index' of the given table
    const VlRtmdDataTypeRow& dataTypeRow(uint32_t index) const {
        return row(m_dataTypesTabpp, index);
    }
    const VlRtmdGlobalSymRow& globalSymRow(uint32_t index) const {
        return row(m_globalSymsTabpp, index);
    }
    const VlRtmdSignalTypeRow& signalTypeRow(uint32_t index) const {
        return row(m_signalTypesTabpp, index);
    }
    const VlRtmdHierRow& hierRow(uint32_t index) const { return row(m_hierTabpp, index); }
    // Returns the activity set handle for given activity set index
    inline VlRtmdActSet actSet(uint32_t index) const;
    // Returns the data type handle for given type index
    inline VlRtmdDataType dataType(uint32_t index) const;
    // Returns the signal type handle for given signal type index
    inline VlRtmdSignalType signalType(uint32_t index) const;
    // Returns the address of the value of the given Signal hierarchy row, or nullptr if the value
    // is not accessible
    inline const void* signalAddress(const VlRtmdHierRow& row) const;
    // Ordering of the descriptors of different models, in the order the models were added to
    // their context, for stability
    bool operator<(const VlRtmd& other) const { return *m_modelp < *other.m_modelp; }
};

//=============================================================================
// Activity set descriptors (corresponds to AstNetlist::actSets() in the compiler)

// Row of the activity set table. The first rows are the range of each set, by set index. The
// rest are the flag numbers of all sets, each set's following the previous.
class VlRtmdActSetRow final {
public:
    // TYPES

    // Range of the rows holding the flag numbers of an activity set
    struct Range final {
        uint32_t m_begin;  // First row
        uint32_t m_end;  // One past the last row
    };

    struct Flag final {
        uint32_t m_flag;  // Activity flag index
    };

private:
    // STATE
    union {
        Range m_range;  // Range of a set, in the first rows
        Flag m_flag;  // Activity flag number, in the rest
    };

public:
    // CONSTRUCTORS
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdActSetRow(const Range& range)
        : m_range{range} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdActSetRow(const Flag& flag)
        : m_flag{flag} {}

    // METHOD
    // The contents of the row, which depends on the row, as above
    const Range& range() const { return m_range; }
    const Flag& flag() const { return m_flag; }
};

// Handle to an activity set used by client code - this is unique for each model and set within it
class VlRtmdActSet final {
    const VlRtmd* m_rtmdp;  // The model's descriptor tables
    uint32_t m_index;  // The index of the set, which is the row of its range

    // The row holding the range of this set
    const VlRtmdActSetRow& row() const {
        assert(m_rtmdp->m_actSetsTabp);
        return m_rtmdp->m_actSetsTabp[m_index];
    }

    // Created by VlRtmd only
    friend class VlRtmd;
    VlRtmdActSet(const VlRtmd* rtmdp, uint32_t index)
        : m_rtmdp{rtmdp}
        , m_index{index} {}

public:
    // Number of activity flags in the set, 0 if the signal has no activity set
    uint32_t size() const {
        if (m_index == VlRtmd::NOIDX) return 0;
        return row().range().m_end - row().range().m_begin;
    }
    // Whether the signal might have changed since the activity flags were last cleared. Without
    // an activity set, it might change at any time. An empty set never changes.
    bool active() const {
        if (m_index == VlRtmd::NOIDX) return true;
        for (uint32_t i = row().range().m_begin; i != row().range().m_end; ++i) {
            if (m_rtmdp->m_activityFlagsp[m_rtmdp->m_actSetsTabp[i].flag().m_flag]) return true;
        }
        return false;
    }

    // Same set of the same model
    bool operator==(const VlRtmdActSet& other) const {
        return m_rtmdp == other.m_rtmdp && m_index == other.m_index;
    }
    // Ordering: by model, then shortest first, then by index
    bool operator<(const VlRtmdActSet& other) const {
        if (m_rtmdp != other.m_rtmdp) return *m_rtmdp < *other.m_rtmdp;
        const uint32_t thisSize = size();
        const uint32_t otherSize = other.size();
        if (thisSize != otherSize) return thisSize < otherSize;
        return m_index < other.m_index;
    }
};

//=============================================================================
// Data types descriptors (corresponds to AstNodeRtmdDataType in the compiler)

// One entry in the data type descriptor table: a descriptor, tagged with its kind. The members of
// a struct or union, and the items of an enum, are the rows following it. Rows are constructed
// from the descriptor, which sets the tag, as C++14 has no designated initializers for unions.
class VlRtmdDataTypeRow final {
public:
    // TYPES

    // A builtin primitive type
    struct Atom final {
        // Base data type of a value
        enum class Kind : uint8_t {
            DOUBLE,
            INTEGER,
            BIT,
            LOGIC,
            INT,
            SHORTINT,
            LONGINT,
            BYTE,
            CHANDLE,
            EVENT,
            TIME,
        };

        Kind m_kind;  // Base data type
        bool m_signed;  // Signed type
        uint32_t m_bits;  // Width
    };

    // An enum over a base type. Its items are the rows following it.
    struct Enum final {
        const char* m_namep;  // Name of the enum
        uint32_t m_baseIdx;  // Base type, as a type table index
        uint32_t m_count;  // Number of items
    };

    // An item of an enum
    struct EnumItem final {
        const char* m_namep;  // Name of the item
        const char* m_valuep;  // Value of the item, as a binary string
    };

    // Member of a struct or union
    struct Member final {
        const char* m_namep;  // Name of the member
        uint32_t m_typeIdx;  // Type of the member, as a type table index
        uint32_t m_offset;  // Unpacked: byte offset of the member. Packed: bit offset of its LSB.
    };

    // Element counts derive from the declared range, see VlRtmdDataType::elements
    struct PackedArray final {
        int32_t m_left;  // Declared range, left index
        int32_t m_right;  // Declared range, right index
        uint32_t m_elemIdx;  // Element type, as a type table index
        bool m_signed;  // Signed type
    };

    // Its members are the rows following it, most significant first
    struct PackedStruct final {
        uint32_t m_count;  // Number of members
        bool m_signed;  // Signed type
    };

    // Members overlay each other, all starting at bit 0. As wide as the widest member. Its members
    // are the rows following it.
    struct PackedUnion final {
        uint32_t m_count;  // Number of members
        bool m_signed;  // Signed type
    };

    struct UnpackedArray final {
        int32_t m_left;  // Declared range, left index
        int32_t m_right;  // Declared range, right index
        uint32_t m_elemIdx;  // Element type, as a type table index
        uint32_t m_elemBytes;  // Bytes per element
    };

    // Its members are the rows following it
    struct UnpackedStruct final {
        uint32_t m_count;  // Number of members
    };

    // The last row of the table
    struct End final {};

private:
    // STATE

    // Kind of the descriptor
    enum class Tag : uint8_t {
        // Proper type
        ATOM,
        ENUM,
        PACKED_ARRAY,
        PACKED_STRUCT,
        PACKED_UNION,
        UNPACKED_ARRAY,
        UNPACKED_STRUCT,
        // Not types, but part of preceding types
        ENUM_ITEM,  // Enum item
        MEMBER,  // Struct or union member
        // Not a type, marks the end of the table
        END
    };

    Tag m_tag;  // Kind of the descriptor
    union {
        Atom m_atom;
        Enum m_enum;
        EnumItem m_enumItem;
        Member m_member;
        PackedArray m_packedArray;
        PackedStruct m_packedStruct;
        PackedUnion m_packedUnion;
        UnpackedArray m_unpackedArray;
        UnpackedStruct m_unpackedStruct;
        End m_end;
    };

public:
    // CONSTRUCTORS
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const Atom& d)
        : m_tag{Tag::ATOM}
        , m_atom{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const Enum& d)
        : m_tag{Tag::ENUM}
        , m_enum{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const EnumItem& d)
        : m_tag{Tag::ENUM_ITEM}
        , m_enumItem{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const Member& d)
        : m_tag{Tag::MEMBER}
        , m_member{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const PackedArray& d)
        : m_tag{Tag::PACKED_ARRAY}
        , m_packedArray{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const PackedStruct& d)
        : m_tag{Tag::PACKED_STRUCT}
        , m_packedStruct{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const PackedUnion& d)
        : m_tag{Tag::PACKED_UNION}
        , m_packedUnion{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const UnpackedArray& d)
        : m_tag{Tag::UNPACKED_ARRAY}
        , m_unpackedArray{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const UnpackedStruct& d)
        : m_tag{Tag::UNPACKED_STRUCT}
        , m_unpackedStruct{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdDataTypeRow(const End& d)
        : m_tag{Tag::END}
        , m_end{d} {}

    // METHODS
    const Atom* atomp() const {
        if (m_tag != Tag::ATOM) return nullptr;
        return &m_atom;
    }
    const Enum* enump() const {
        if (m_tag != Tag::ENUM) return nullptr;
        return &m_enum;
    }
    const EnumItem* enumItemp() const {
        if (m_tag != Tag::ENUM_ITEM) return nullptr;
        return &m_enumItem;
    }
    const Member* memberp() const {
        if (m_tag != Tag::MEMBER) return nullptr;
        return &m_member;
    }
    const PackedArray* packedArrayp() const {
        if (m_tag != Tag::PACKED_ARRAY) return nullptr;
        return &m_packedArray;
    }
    const PackedStruct* packedStructp() const {
        if (m_tag != Tag::PACKED_STRUCT) return nullptr;
        return &m_packedStruct;
    }
    const PackedUnion* packedUnionp() const {
        if (m_tag != Tag::PACKED_UNION) return nullptr;
        return &m_packedUnion;
    }
    const UnpackedArray* unpackedArrayp() const {
        if (m_tag != Tag::UNPACKED_ARRAY) return nullptr;
        return &m_unpackedArray;
    }
    const UnpackedStruct* unpackedStructp() const {
        if (m_tag != Tag::UNPACKED_STRUCT) return nullptr;
        return &m_unpackedStruct;
    }

    bool isEnd() const { return m_tag == Tag::END; }

    bool isType() const {
        switch (m_tag) {
        case Tag::ATOM:
        case Tag::ENUM:
        case Tag::PACKED_ARRAY:
        case Tag::PACKED_STRUCT:
        case Tag::PACKED_UNION:
        case Tag::UNPACKED_ARRAY:
        case Tag::UNPACKED_STRUCT: return true;
        default: return false;
        }
    }
};

// Handle to a data type used by client code - this is unique for each model and type within it
class VlRtmdDataType final {
    const VlRtmd* m_rtmdp;  // The model's descriptor tables
    uint32_t m_index;  // The index of the type in the data type table

    // The row of this type, or the one 'offset' rows after it
    const VlRtmdDataTypeRow& row(uint32_t offset = 0) const {
        return m_rtmdp->dataTypeRow(m_index + offset);
    }
    // Keyword of a builtin type, and whether it is signed by default
    const char* atomKeyword(bool& signedByDefault) const;

    // Created by VlRtmd only
    friend class VlRtmd;
    VlRtmdDataType(const VlRtmd* rtmdp, uint32_t index)
        : m_rtmdp{rtmdp}
        , m_index{index} {
        assert(row().isType());
    }

public:
    // TYPES
    using AtomKind = VlRtmdDataTypeRow::Atom::Kind;
    // How a value of a type is stored
    enum class StorageKind : uint8_t {  //
        CDATA,
        SDATA,
        IDATA,
        QDATA,
        WDATA,
        DOUBLE,
        EVENT
    };

    // SystemVerilog declared elements iff array type. Will crash on other type.
    uint32_t elements() const;
    // SystemVerilog declared bit width iff packed type. Will crash if not packed type.
    uint32_t width() const;
    // Render as a string, similar to $typename
    std::string toString() const;

    // Name of an enum type
    const char* enumName() const {
        assert(row().enump());
        return row().enump()->m_namep;
    }
    // Number of items of an enum type
    uint32_t enumItemCount() const {
        assert(row().enump());
        return row().enump()->m_count;
    }
    // The given enum item of an enum type
    const VlRtmdDataTypeRow::EnumItem& enumItem(uint32_t i) const {
        assert(row().enump());
        return *row(1 + i).enumItemp();  // following rows
    }
    // The given member of a struct or union, which are the rows following it
    const VlRtmdDataTypeRow::Member& member(uint32_t i) const {
        assert(i < memberCount());
        return *row(1 + i).memberp();  // following rows
    }
    // Number of members of a struct or union
    uint32_t memberCount() const;
    // The type of the given member of a struct or union
    inline VlRtmdDataType memberType(uint32_t i) const;

    // Whether a builtin type
    bool isAtom() const { return row().atomp(); }
    // Whether an enum
    bool isEnum() const { return row().enump(); }
    // The base type of an enum
    inline VlRtmdDataType enumBase() const;
    // Whether an unpacked array
    bool isUnpackedArray() const { return row().unpackedArrayp(); }
    // Whether an unpacked struct
    bool isUnpackedStruct() const { return row().unpackedStructp(); }
    // Whether a packed array
    bool isPackedArray() const { return row().packedArrayp(); }
    // Whether a packed struct
    bool isPackedStruct() const { return row().packedStructp(); }
    // Whether a packed union
    bool isPackedUnion() const { return row().packedUnionp(); }
    // The element type of an array
    inline VlRtmdDataType elemType() const;
    // Declared range of an array
    int32_t left() const;
    int32_t right() const;
    // Bytes per element of an unpacked array
    uint32_t elemBytes() const {
        assert(row().unpackedArrayp());
        return row().unpackedArrayp()->m_elemBytes;
    }
    // The kind of a builtin type. Will crash on other types.
    AtomKind atomKind() const;
    // How a value of a packed or atom type is stored
    StorageKind storageKind() const;
    // How an integral value of the given width is stored
    static StorageKind storageKind(uint32_t bits);

    // Ordering, e.g. for use as a map key
    bool operator<(const VlRtmdDataType& other) const {
        if (m_rtmdp != other.m_rtmdp) return *m_rtmdp < *other.m_rtmdp;
        return m_index < other.m_index;
    }
};

//=============================================================================
// Signal types descriptors (corresponds to AstRtmdSignalType in the compiler)

// One entry in the signal type table: a descriptor. There is only one kind, so it needs no tag.
class VlRtmdSignalTypeRow final {
public:
    // How a signal is declared: kind, direction and the type of its value
    struct Signal final {
        // Kind of variable or net a signal is declared as
        enum class Kind : uint8_t {
            // Note: Entries must match VRtmdSignalKind (by name, not necessarily by value)
            VAR,
            WIRE,
            WREAL,
            TRI,
            TRI0,
            TRI1,
            TRIAND,
            TRIOR,
            SUPPLY0,
            SUPPLY1,
            GPARAM,  // Module parameter
            LPARAM,  // localparam
            SPECPARAM,
            GENVAR,
        };

        // Declared direction of a port, or NONE for anything that is not one
        enum class Direction : uint8_t {
            // Note: Entries must match VDirection (by name, not necessarily by value)
            NONE,
            INPUT,
            OUTPUT,
            INOUT,
            REF,
            CONSTREF,
        };

        Kind m_kind;  // Signal kind, e.g. VAR, WIRE, PARAM
        Direction m_direction;  // NONE if it is not a port
        uint32_t m_typeIdx;  // Type of the value, as a type table index
    };

private:
    union {
        Signal m_signal;
    };

public:
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdSignalTypeRow(const Signal& d)
        : m_signal{d} {}

    // The descriptor of the row
    const Signal* signalp() const { return &m_signal; }
};

// Handle to a signal type used by client code - this is unique for each model and type within it
class VlRtmdSignalType final {
    const VlRtmd* m_rtmdp;  // The model's descriptor tables
    uint32_t m_index;  // The index of the type in the signal type table

    // The row of this type
    const VlRtmdSignalTypeRow& row() const { return m_rtmdp->signalTypeRow(m_index); }

    // Created by VlRtmd only
    friend class VlRtmd;
    VlRtmdSignalType(const VlRtmd* rtmdp, uint32_t index)
        : m_rtmdp{rtmdp}
        , m_index{index} {}

public:
    // TYPES
    using Kind = VlRtmdSignalTypeRow::Signal::Kind;
    using Direction = VlRtmdSignalTypeRow::Signal::Direction;

    // Kind of variable or net the signal is declared as
    Kind kind() const { return row().signalp()->m_kind; }
    // Declared direction, NONE if not a port
    Direction direction() const { return row().signalp()->m_direction; }
    // Type of the value
    VlRtmdDataType dataType() const { return m_rtmdp->dataType(row().signalp()->m_typeIdx); }
};

//=============================================================================
// Global descriptors (corresponds to the constant pool entries described in the compiler)

// One entry in the global table: a descriptor. There is only one kind, so it needs no tag.
class VlRtmdGlobalSymRow final {
public:
    // A global constant
    struct Const final {
        const void* m_datap;  // Address of the constant
    };

private:
    union {
        Const m_const;
    };

public:
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdGlobalSymRow(const Const& d)
        : m_const{d} {}

    // The descriptor of the row
    const Const* constp() const { return &m_const; }
};

//=============================================================================
// Hierarchy descriptors (corresponds to AstNodeRtmdItem in the compiler)

// One entry in the hierarchy table: a descriptor, tagged with its kind. Rows are constructed from
// the descriptor, which sets the tag, as C++14 has no designated initializers for unions.
class VlRtmdHierRow final {
public:
    // Flags for hierarchy descriptors
    class HierFlags final {
        const uint32_t m_flags;  // The flags

    public:
        enum : uint32_t {
            HAS_SIGNALS = 1 << 0,  // At least one signal is declared under the level
            HAS_TRACED_SIGNALS = 1 << 1,  // At least one traced signal is declared under the level
        };

        // cppcheck-suppress noExplicitConstructor
        /* implicit */ constexpr HierFlags(uint32_t flags)
            : m_flags{flags} {}

        bool hasSignals() const { return m_flags & HAS_SIGNALS; }
        bool hasTracedSignals() const { return m_flags & HAS_TRACED_SIGNALS; }
    };

    // Flags for signal descriptors
    class SignalFlags final {
        const uint32_t m_flags;  // The flags

    public:
        enum : uint32_t {
            IS_GLOBAL = 1 << 0,  // The value is a global, e.g. a constant pool entry
            IS_TRACED = 1 << 1,  // Signal is traced
        };

        // cppcheck-suppress noExplicitConstructor
        /* implicit */ constexpr SignalFlags(uint32_t flags)
            : m_flags{flags} {}

        bool isGlobal() const { return m_flags & IS_GLOBAL; }
        bool isTraced() const { return m_flags & IS_TRACED; }
    };

    // Open a hierarchy level
    struct Push final {
        // Kind of design scope a level is
        enum class Kind : uint8_t {
            // Note: Entries must match VRtmdHierKind (by name, not necessarily by value)
            ROOT,
            ROOTIO,  // The variables of the root module
            MODULE,
            INTERFACE,
            PACKAGE,
            GENERATE,
            BEGIN,
            FORK,
            FUNCTION,
            TASK,
        };

        const char* m_namep;  // Name of the level
        Kind m_kind;  // Kind of the level
        HierFlags m_flags;  // Flags of the push
    };

    // Close the level the matching Push opened
    struct Pop final {};

    // A value, located by offset from the symbol table, or via the global table for globals
    struct Signal final {
        const char* m_namep;  // Name of the signal
        uint32_t m_typeIdx;  // Signal type, as a signal type table index
        uint32_t m_actSetIdx;  // Activity set table index
        size_t m_addr;  // Offset from the symbol table/index in global table/VlRtmd::NOADDR
        SignalFlags m_flags;  // Flags of the signal
    };

    // An instance: the level that follows is the instantiated scope
    struct Instance final {
        const char* m_namep;  // Name of the instance
    };

    // An interface reference
    struct IfaceRef final {
        const char* m_namep;  // Name of the interface reference variable
        uint32_t m_pushIdx;  // Row index of the target interface instance Push
    };

    // A partition: a separately verilated model, which has its own RTMD
    struct Partition final {
        const char* m_namep;  // Name of the instance
    };

private:
    // Kind of the descriptor
    enum class Tag : uint8_t {
        PUSH,
        POP,
        SIGNAL,
        INSTANCE,
        IFACEREF,
        PARTITION,
    };

    Tag m_tag;  // Kind of the descriptor
    union {
        Push m_push;
        Pop m_pop;
        Signal m_signal;
        Instance m_instance;
        IfaceRef m_ifaceRef;
        Partition m_partition;
    };

public:
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdHierRow(const Push& d)
        : m_tag{Tag::PUSH}
        , m_push{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdHierRow(const Pop& d)
        : m_tag{Tag::POP}
        , m_pop{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdHierRow(const Signal& d)
        : m_tag{Tag::SIGNAL}
        , m_signal{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdHierRow(const Instance& d)
        : m_tag{Tag::INSTANCE}
        , m_instance{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdHierRow(const IfaceRef& d)
        : m_tag{Tag::IFACEREF}
        , m_ifaceRef{d} {}
    // cppcheck-suppress noExplicitConstructor
    /* implicit */ constexpr VlRtmdHierRow(const Partition& d)
        : m_tag{Tag::PARTITION}
        , m_partition{d} {}

    // The descriptor of the row, or nullptr if the row holds a different kind of descriptor
    const Push* pushp() const {
        if (m_tag != Tag::PUSH) return nullptr;
        return &m_push;
    }
    const Pop* popp() const {
        if (m_tag != Tag::POP) return nullptr;
        return &m_pop;
    }
    const Signal* signalp() const {
        if (m_tag != Tag::SIGNAL) return nullptr;
        return &m_signal;
    }
    const Instance* instancep() const {
        if (m_tag != Tag::INSTANCE) return nullptr;
        return &m_instance;
    }
    const IfaceRef* ifaceRefp() const {
        if (m_tag != Tag::IFACEREF) return nullptr;
        return &m_ifaceRef;
    }
    const Partition* partitionp() const {
        if (m_tag != Tag::PARTITION) return nullptr;
        return &m_partition;
    }
};

//=============================================================================
// VlRtmd inline methods

VlRtmdActSet VlRtmd::actSet(uint32_t index) const {  //
    return VlRtmdActSet{this, index};
}

VlRtmdDataType VlRtmd::dataType(uint32_t index) const {  //
    return VlRtmdDataType{this, index};
}

VlRtmdDataType VlRtmdDataType::memberType(uint32_t i) const {
    return m_rtmdp->dataType(member(i).m_typeIdx);
}

VlRtmdDataType VlRtmdDataType::enumBase() const {
    assert(row().enump());
    return m_rtmdp->dataType(row().enump()->m_baseIdx);
}

VlRtmdDataType VlRtmdDataType::elemType() const {
    if (const VlRtmdDataTypeRow::PackedArray* const arrayp = row().packedArrayp()) {
        return m_rtmdp->dataType(arrayp->m_elemIdx);
    }
    if (const VlRtmdDataTypeRow::UnpackedArray* const arrayp = row().unpackedArrayp()) {
        return m_rtmdp->dataType(arrayp->m_elemIdx);
    }
    // LCOV_EXCL_START
    VL_FATAL_MT(__FILE__, __LINE__, "", "VlRtmdDataType::elemType called on a non array type");
    return *this;
    // LCOV_EXCL_STOP
}

VlRtmdSignalType VlRtmd::signalType(uint32_t index) const {  //
    return VlRtmdSignalType{this, index};
}

const void* VlRtmd::signalAddress(const VlRtmdHierRow& row) const {
    assert(row.signalp());
    const VlRtmdHierRow::Signal& signal = *row.signalp();
    // No address if the value is not accessible
    if (signal.m_addr == NOADDR) return nullptr;
    // A global is located via the global table
    if (signal.m_flags.isGlobal()) return globalSymRow(signal.m_addr).constp()->m_datap;
    // Others by offset from the symbol table
    return static_cast<const uint8_t*>(m_symsp) + signal.m_addr;
}

//=============================================================================
// Listener class that enumerates hierarchy of all models in a context in a canonical form

class VlRtmdHierListener VL_NOT_FINAL {
    // TYPES
    // The path from the root model to the current hierarchy table entry: the enclosing levels,
    // outermost first, across the models walked as partitions
    class Path final {
        // Built by the walk only
        friend class VlRtmdHierListener;

        // A level: the row naming it, and its Push. The row is the Instance row of an instance,
        // except for the top instance of a partition, which is named by the Partition row. It
        // is the IfaceRef row of an interface reference, whose Push is that of the referenced
        // interface. Otherwise it is the Push row itself.
        using Entry = std::pair<const VlRtmdHierRow*, const VlRtmdHierRow::Push*>;

        const VerilatedModel* m_rootp = nullptr;  // The root model
        std::vector<Entry> m_entries;  // The levels

        void root(const VerilatedModel& model) {
            assert(m_entries.empty());
            m_rootp = &model;
        }
        void push(const VlRtmdHierRow* rowp, const VlRtmdHierRow::Push* pushp) {
            m_entries.emplace_back(rowp, pushp);
        }
        void pop() { m_entries.pop_back(); }
        const Entry& back() const { return m_entries.back(); }
        size_t size() const { return m_entries.size(); }

    public:
        // The hierarchical name of the innermost level, as %m would give it
        std::string name() const;
    };

    // STATE
    // The models of the context being walked, by hierarchical name
    std::map<std::string, VerilatedModel*> m_models;
    std::set<const VerilatedModel*> m_walked;  // The models walked so far
    Path m_path;  // The path to the current entry
    // The path depth of the level the listener declined to enter, whose contents are skipped,
    // or 0 if not skipping. Kept across walking partitions within it, as they are part of that
    // level, and the path continues into them.
    size_t m_skipDepth = 0;

    // Internal to 'walkContext': Walks the hierarchy table of the given model. 'partitionRowp'
    // is the Partition row it is walked for, otherwise nullptr.
    void walkModel(const VerilatedModel& model, const VlRtmdHierRow* partitionRowp);
    // Internal to 'walkContext': Walks the rows of 'model' from given row index
    void walkRows(const VerilatedModel& model, const VlRtmdHierRow* partitionRowp,
                  uint32_t rowIdx);
    // Internal to 'walkContext': Reports the components of a signal recursively
    void walkDtype(const char* namep, const VlRtmdSignalType& sigType, const VlRtmdDataType& dtype,
                   const VlRtmdActSet& actSet, const uint8_t* datap, uint32_t lsb);

public:
    virtual ~VlRtmdHierListener() = default;

    // Enumerate the hierarchy of all models in the context, calling the LISTENER methods.
    // The enumeration is normalized so partition instances appear as normal instances.
    void walkContext(const VerilatedContext& context);

protected:
    // TYPES
    enum class InstanceKind : uint8_t { MODULE, INTERFACE, PACKAGE };
    enum class ScopeKind : uint8_t { ROOTIO, FUNCTION, TASK, GENERATE, BEGIN, FORK };
    using HierFlags = VlRtmdHierRow::HierFlags;
    using SignalFlags = VlRtmdHierRow::SignalFlags;

    // CONSTANTS
    // The 'lsb' of a component that is not within a packed value, see 'onComponent'
    static constexpr uint32_t NOLSB = ~0U;

    // METHODS
    // The hierarchical name of the current hierarchy level, as %m would give it
    std::string pathName() const { return m_path.name(); }

    // LISTENERS
    // The 'enter' methods return whether to walk into the level. If false, nothing within it
    // is reported, including the matching 'exit'. The 'exit' methods are passed the same
    // arguments as the matching 'enter'. 'flags' tell whether anything within the level is a
    // signal, and a traced signal, see HierFlags. A root is assumed to have both.

    // Enter and exit a root model, called for all models not used as a partition
    virtual bool enterRoot(const VerilatedModel& model) = 0;
    virtual void exitRoot(const VerilatedModel& model) = 0;
    // Enter and exit an instance, aka AstCell, but partition aware
    virtual bool enterInstance(InstanceKind kind, const char* namep, const char* modNamep,
                               HierFlags flags)
        = 0;
    virtual void exitInstance(InstanceKind kind, const char* namep, const char* modNamep,
                              HierFlags flags)
        = 0;
    // Enter and exit an interface reference scope
    virtual bool enterIfaceRef(const char* namep, const char* modNamep, HierFlags flags) = 0;
    virtual void exitIfaceRef(const char* namep, const char* modNamep, HierFlags flags) = 0;
    // Enter and exit a root IO level, function, task, generate block, begin block, or fork
    // block scope
    virtual bool enterScope(ScopeKind kind, const char* namep, HierFlags flags) = 0;
    virtual void exitScope(ScopeKind kind, const char* namep, HierFlags flags) = 0;
    // Called for each signal in the model. 'sigType' is that of the signal, 'dtype' that of the
    // value reported. 'datap' is the address of the value, or nullptr if not accessible.
    // 'flags' tell whether it is traced, see SignalFlags. Return whether to walk the components
    // of an array, struct or union value, otherwise the return value is ignored.
    virtual bool onSignal(const char* namep, const VlRtmdSignalType& sigType,
                          const VlRtmdDataType& dtype, const VlRtmdActSet& actSet,
                          const void* datap, SignalFlags flags)
        = 0;

    // Enter and exit the components of an array, struct or union value, around their reports,
    // if 'onSignal' or 'onComponent' returned true for it. 'namep' is the name it was reported as.
    virtual void enterUnpackedArray(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void exitUnpackedArray(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void enterUnpackedStruct(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void exitUnpackedStruct(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void enterPackedArray(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void exitPackedArray(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void enterPackedStruct(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void exitPackedStruct(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void enterPackedUnion(const char* namep, const VlRtmdDataType& dtype) = 0;
    virtual void exitPackedUnion(const char* namep, const VlRtmdDataType& dtype) = 0;

    // Called for each component of an array, struct or union value that is being walked, as
    // 'onSignal'. 'namep' is the name of a struct or union member, or the index of an array
    // element, as e.g. "[3]". A component of a packed value is at bit offset 'lsb' of the value
    // at 'datap', which is that of the outermost packed value. Otherwise 'lsb' is NOLSB.
    virtual bool onComponent(const char* namep, const VlRtmdSignalType& sigType,
                             const VlRtmdDataType& dtype, const VlRtmdActSet& actSet,
                             const void* datap, uint32_t lsb)
        = 0;
};

#endif  // Guard
