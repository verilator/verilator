// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3AST_H_
#define VERILATOR_V3AST_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Broken.h"
#include "V3Error.h"
#include "V3FileLine.h"
#include "V3FunctionTraits.h"
#include "V3Global.h"
#include "V3Number.h"
#include "V3StdFuture.h"

#include "V3Ast__gen_forward_class_decls.h"  // From ./astgen

#include <cmath>
#include <functional>
#include <map>
#include <set>
#include <type_traits>
#include <unordered_set>
#include <utility>
#include <vector>

// Forward declarations
class V3Graph;
class ExecMTask;

// Hint class so we can choose constructors
class VFlagLogicPacked {};
class VFlagBitPacked {};
class VFlagChildDType {};  // Used by parser.y to select constructor that sets childDType

// Used as key for another map, needs operator<, hence not an unordered_set
using MTaskIdSet = std::set<int>;  // Set of mtaskIds for Var sorting

//######################################################################

// For broken() function, return error string if have a match
#define BROKEN_RTN(test) \
    do { \
        if (VL_UNCOVERABLE(test)) return "'" #test "' @ " __FILE__ ":" VL_STRINGIFY(__LINE__); \
    } while (false)
// For broken() function, return error string if a base of this class has a match
#define BROKEN_BASE_RTN(test) \
    do { \
        const char* const reasonp = (test); \
        if (VL_UNCOVERABLE(reasonp)) return reasonp; \
    } while (false)

// (V)erilator (N)ode is: Returns true if and only if AstNode is of the given AstNode subtype,
// and not nullptr.
#define VN_IS(nodep, nodetypename) (AstNode::privateIs<Ast##nodetypename, decltype(nodep)>(nodep))

// (V)erilator (N)ode cast: Similar to dynamic_cast, but more efficient, use this instead.
// Cast to given type if node is of such type, otherwise returns nullptr. If 'nodep' is nullptr,
// return nullptr. Pointer constness is preserved, i.e.: given a 'const AstNode*',
// a 'const Ast<nodetypename>*' is returned.
#define VN_CAST(nodep, nodetypename) \
    (AstNode::privateCast<Ast##nodetypename, decltype(nodep)>(nodep))

// (V)erilator (N)ode as: Assert node is of given type then cast to that type. Use this to
// downcast instead of VN_CAST when you know the true type of the node. If 'nodep' is nullptr,
// return nullptr. Pointer constness is preserved, i.e.: given a 'const AstNode*', a 'const
// Ast<nodetypename>*' is returned.
#define VN_AS(nodep, nodetypename) (AstNode::privateAs<Ast##nodetypename, decltype(nodep)>(nodep))

// (V)erilator (N)ode deleted: Pointer to deleted AstNode (for assertions only)
#define VN_DELETED(nodep) VL_UNLIKELY((uint64_t)(nodep) == 0x1)

//######################################################################

class VNType final {
public:
#include "V3Ast__gen_type_enum.h"  // From ./astgen
    // Above include has:
    //   enum en {...};
    //   const char* ascii() const {...};
    enum en m_e;
    // cppcheck-suppress uninitVar  // responsibility of each subclass
    VNType() = default;
    // cppcheck-suppress noExplicitConstructor
    constexpr VNType(en _e) VL_MT_SAFE : m_e{_e} {}
    explicit VNType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const VL_MT_SAFE { return m_e; }
};
constexpr bool operator==(const VNType& lhs, const VNType& rhs) VL_MT_SAFE {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VNType& lhs, VNType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VNType::en lhs, const VNType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VNType& rhs) { return os << rhs.ascii(); }

// ######################################################################

class VLifetime final {
public:
    enum en : uint8_t { NONE, AUTOMATIC, STATIC };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {"NONE", "VAUTOM", "VSTATIC"};
        return names[m_e];
    }
    VLifetime()
        : m_e{NONE} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VLifetime(en _e)
        : m_e{_e} {}
    explicit VLifetime(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    bool isNone() const { return m_e == NONE; }
    bool isAutomatic() const { return m_e == AUTOMATIC; }
    bool isStatic() const { return m_e == STATIC; }
};
constexpr bool operator==(const VLifetime& lhs, const VLifetime& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VLifetime& lhs, VLifetime::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VLifetime::en lhs, const VLifetime& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VLifetime& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

class VAccess final {
public:
    enum en : uint8_t {
        READ,  // Read/Consumed, variable not changed
        WRITE,  // Written/Updated, variable might be updated, but not consumed
        //      // so variable might be removable if not consumed elsewhere
        READWRITE,  // Read/Consumed and written/updated, variable both set and
        //          // also consumed, cannot remove usage of variable.
        //          // For non-simple data types only e.g. no tristates/delayed vars.
        NOCHANGE  // No change to previous state, used only in V3LinkLValue
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {"RD", "WR", "RW", "--"};
        return names[m_e];
    }
    const char* arrow() const {
        static const char* const names[] = {"[RV] <-", "[LV] =>", "[LV] <=>", "--"};
        return names[m_e];
    }
    VAccess()
        : m_e{READ} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VAccess(en _e)
        : m_e{_e} {}
    explicit VAccess(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    VAccess invert() const {
        return (m_e == READWRITE) ? VAccess{m_e} : (m_e == WRITE ? VAccess{READ} : VAccess{WRITE});
    }
    bool isReadOnly() const { return m_e == READ; }  // False with READWRITE
    bool isWriteOnly() const { return m_e == WRITE; }  // False with READWRITE
    bool isReadOrRW() const { return m_e == READ || m_e == READWRITE; }
    bool isWriteOrRW() const { return m_e == WRITE || m_e == READWRITE; }
    bool isRW() const { return m_e == READWRITE; }
};
constexpr bool operator==(const VAccess& lhs, const VAccess& rhs) { return lhs.m_e == rhs.m_e; }
constexpr bool operator==(const VAccess& lhs, VAccess::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VAccess::en lhs, const VAccess& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VAccess& rhs) { return os << rhs.ascii(); }

// ######################################################################

class VSigning final {
public:
    enum en : uint8_t {
        UNSIGNED,
        SIGNED,
        NOSIGN,
        _ENUM_MAX  // Leave last
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {"UNSIGNED", "SIGNED", "NOSIGN"};
        return names[m_e];
    }
    VSigning()
        : m_e{UNSIGNED} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VSigning(en _e)
        : m_e{_e} {}
    static VSigning fromBool(bool isSigned) {  // Factory method
        return isSigned ? VSigning{SIGNED} : VSigning{UNSIGNED};
    }
    explicit VSigning(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    bool isSigned() const VL_MT_SAFE { return m_e == SIGNED; }
    bool isNosign() const VL_MT_SAFE { return m_e == NOSIGN; }
    // No isUnsigned() as it's ambiguous if NOSIGN should be included or not.
};
constexpr bool operator==(const VSigning& lhs, const VSigning& rhs) { return lhs.m_e == rhs.m_e; }
constexpr bool operator==(const VSigning& lhs, VSigning::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VSigning::en lhs, const VSigning& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VSigning& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

class VPragmaType final {
public:
    enum en : uint8_t {
        ILLEGAL,
        COVERAGE_BLOCK_OFF,
        HIER_BLOCK,
        INLINE_MODULE,
        NO_INLINE_MODULE,
        NO_INLINE_TASK,
        PUBLIC_MODULE,
        PUBLIC_TASK,
        FULL_CASE,
        PARALLEL_CASE,
        ENUM_SIZE
    };
    enum en m_e;
    VPragmaType()
        : m_e{ILLEGAL} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VPragmaType(en _e)
        : m_e{_e} {}
    explicit VPragmaType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
};
constexpr bool operator==(const VPragmaType& lhs, const VPragmaType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VPragmaType& lhs, VPragmaType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VPragmaType::en lhs, const VPragmaType& rhs) { return lhs == rhs.m_e; }

// ######################################################################

class VEdgeType final {
public:
    // REMEMBER to edit the strings below too
    enum en : uint8_t {
        // These must be in general -> most specific order, as we sort by it
        // in V3Const::visit AstSenTree
        ET_ILLEGAL,
        // Involving a variable
        ET_CHANGED,  // Value changed
        ET_BOTHEDGE,  // POSEDGE | NEGEDGE (i.e.: 'edge' in Verilog)
        ET_POSEDGE,
        ET_NEGEDGE,
        ET_EVENT,  // VlEvent::isFired
        // Involving an expression
        ET_TRUE,
        //
        ET_COMBO,  // Sensitive to all combo inputs to this block
        ET_HYBRID,  // This is like ET_COMB, but with explicit sensitivity to an expression
        ET_STATIC,  // static variable initializers (runs before 'initial')
        ET_INITIAL,  // 'initial' statements
        ET_FINAL,  // 'final' statements
        ET_NEVER  // Never occurs (optimized away)
    };
    enum en m_e;
    bool clockedStmt() const {
        static const bool clocked[] = {
            false,  // ET_ILLEGAL

            true,  // ET_CHANGED
            true,  // ET_BOTHEDGE
            true,  // ET_POSEDGE
            true,  // ET_NEGEDGE
            true,  // ET_EVENT
            true,  // ET_TRUE

            false,  // ET_COMBO
            false,  // ET_HYBRID
            false,  // ET_STATIC
            false,  // ET_INITIAL
            false,  // ET_FINAL
            false,  // ET_NEVER
        };
        return clocked[m_e];
    }
    bool anEdge() const { return m_e == ET_BOTHEDGE || m_e == ET_POSEDGE || m_e == ET_NEGEDGE; }
    VEdgeType invert() const {
        switch (m_e) {
        case ET_CHANGED: return ET_CHANGED;
        case ET_BOTHEDGE: return ET_BOTHEDGE;
        case ET_POSEDGE: return ET_NEGEDGE;
        case ET_NEGEDGE: return ET_POSEDGE;
        default: UASSERT_STATIC(0, "Inverting bad edgeType()");
        }
        return VEdgeType::ET_ILLEGAL;
    }
    const char* ascii() const {
        static const char* const names[]
            = {"%E-edge", "CHANGED", "BOTH",   "POS",     "NEG",   "EVENT", "TRUE",
               "COMBO",   "HYBRID",  "STATIC", "INITIAL", "FINAL", "NEVER"};
        return names[m_e];
    }
    const char* verilogKwd() const {
        static const char* const names[]
            = {"%E-edge", "[changed]", "edge",     "posedge",   "negedge", "[event]", "[true]",
               "*",       "[hybrid]",  "[static]", "[initial]", "[final]", "[never]"};
        return names[m_e];
    }
    // Return true iff this and the other have mutually exclusive transitions
    bool exclusiveEdge(const VEdgeType& other) const {
        switch (m_e) {
        case VEdgeType::ET_POSEDGE:
            if (other.m_e == VEdgeType::ET_NEGEDGE) return true;
            break;
        case VEdgeType::ET_NEGEDGE:
            if (other.m_e == VEdgeType::ET_POSEDGE) return true;
            break;
        default: break;
        }
        return false;
    }
    VEdgeType()
        : m_e{ET_ILLEGAL} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VEdgeType(en _e)
        : m_e{_e} {}
    explicit VEdgeType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
};
constexpr bool operator==(const VEdgeType& lhs, const VEdgeType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VEdgeType& lhs, VEdgeType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VEdgeType::en lhs, const VEdgeType& rhs) { return lhs == rhs.m_e; }

// ######################################################################

class VAttrType final {
public:
    // clang-format off
    enum en: uint8_t  {
        ILLEGAL,
        //
        DIM_BITS,                       // V3Const converts to constant
        DIM_DIMENSIONS,                 // V3Width converts to constant
        DIM_HIGH,                       // V3Width processes
        DIM_INCREMENT,                  // V3Width processes
        DIM_LEFT,                       // V3Width processes
        DIM_LOW,                        // V3Width processes
        DIM_RIGHT,                      // V3Width processes
        DIM_SIZE,                       // V3Width processes
        DIM_UNPK_DIMENSIONS,            // V3Width converts to constant
        //
        DT_PUBLIC,                      // V3LinkParse moves to AstTypedef::attrPublic
        //
        ENUM_BASE,                      // V3LinkResolve creates for AstPreSel, V3LinkParam removes
        ENUM_FIRST,                     // V3Width processes
        ENUM_LAST,                      // V3Width processes
        ENUM_NUM,                       // V3Width processes
        ENUM_NEXT,                      // V3Width processes
        ENUM_PREV,                      // V3Width processes
        ENUM_NAME,                      // V3Width processes
        ENUM_VALID,                     // V3Width processes
        //
        MEMBER_BASE,                    // V3LinkResolve creates for AstPreSel, V3LinkParam removes
        //
        TYPENAME,                       // V3Width processes
        //
        VAR_BASE,                       // V3LinkResolve creates for AstPreSel, V3LinkParam removes
        VAR_CLOCK_ENABLE,               // Ignored, accepted for compatibility
        VAR_FORCEABLE,                  // V3LinkParse moves to AstVar::isForceable
        VAR_PUBLIC,                     // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT,                // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT_RD,             // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT_RW,             // V3LinkParse moves to AstVar::sigPublic
        VAR_ISOLATE_ASSIGNMENTS,        // V3LinkParse moves to AstVar::attrIsolateAssign
        VAR_SC_BV,                      // V3LinkParse moves to AstVar::attrScBv
        VAR_SFORMAT,                    // V3LinkParse moves to AstVar::attrSFormat
        VAR_CLOCKER,                    // V3LinkParse moves to AstVar::attrClocker
        VAR_NO_CLOCKER,                 // V3LinkParse moves to AstVar::attrClocker
        VAR_SPLIT_VAR                   // V3LinkParse moves to AstVar::attrSplitVar
    };
    // clang-format on
    enum en m_e;
    const char* ascii() const {
        // clang-format off
        static const char* const names[] = {
            "%E-AT",
            "DIM_BITS", "DIM_DIMENSIONS", "DIM_HIGH", "DIM_INCREMENT", "DIM_LEFT",
            "DIM_LOW", "DIM_RIGHT", "DIM_SIZE", "DIM_UNPK_DIMENSIONS",
            "DT_PUBLIC",
            "ENUM_BASE", "ENUM_FIRST", "ENUM_LAST", "ENUM_NUM",
            "ENUM_NEXT", "ENUM_PREV", "ENUM_NAME", "ENUM_VALID",
            "MEMBER_BASE",
            "TYPENAME",
            "VAR_BASE", "VAR_CLOCK_ENABLE", "VAR_FORCEABLE", "VAR_PUBLIC",
            "VAR_PUBLIC_FLAT", "VAR_PUBLIC_FLAT_RD", "VAR_PUBLIC_FLAT_RW",
            "VAR_ISOLATE_ASSIGNMENTS", "VAR_SC_BV", "VAR_SFORMAT", "VAR_CLOCKER",
            "VAR_NO_CLOCKER", "VAR_SPLIT_VAR"
        };
        // clang-format on
        return names[m_e];
    }
    VAttrType()
        : m_e{ILLEGAL} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VAttrType(en _e)
        : m_e{_e} {}
    explicit VAttrType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
};
constexpr bool operator==(const VAttrType& lhs, const VAttrType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VAttrType& lhs, VAttrType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VAttrType::en lhs, const VAttrType& rhs) { return lhs == rhs.m_e; }

// ######################################################################

class VBasicDTypeKwd final {
public:
    enum en : uint8_t {
        UNKNOWN,
        BIT,
        BYTE,
        CHANDLE,
        EVENT,
        INT,
        INTEGER,
        LOGIC,
        LONGINT,
        DOUBLE,
        SHORTINT,
        TIME,
        // Closer to a class type, but limited usage
        STRING,
        // Internal types for mid-steps
        SCOPEPTR,
        CHARPTR,
        MTASKSTATE,
        TRIGGERVEC,
        DELAY_SCHEDULER,
        TRIGGER_SCHEDULER,
        DYNAMIC_TRIGGER_SCHEDULER,
        FORK_SYNC,
        // Unsigned and two state; fundamental types
        UINT32,
        UINT64,
        // Internal types, eliminated after parsing
        LOGIC_IMPLICIT,
        // Leave last
        _ENUM_MAX
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {"%E-unk",
                                            "bit",
                                            "byte",
                                            "chandle",
                                            "event",
                                            "int",
                                            "integer",
                                            "logic",
                                            "longint",
                                            "real",
                                            "shortint",
                                            "time",
                                            "string",
                                            "VerilatedScope*",
                                            "char*",
                                            "VlMTaskState",
                                            "VlTriggerVec",
                                            "VlDelayScheduler",
                                            "VlTriggerScheduler",
                                            "VlDynamicTriggerScheduler",
                                            "VlFork",
                                            "IData",
                                            "QData",
                                            "LOGIC_IMPLICIT",
                                            " MAX"};
        return names[m_e];
    }
    const char* dpiType() const {
        static const char* const names[]
            = {"%E-unk",        "svBit",         "char",         "void*",           "char",
               "int",           "%E-integer",    "svLogic",      "long long",       "double",
               "short",         "%E-time",       "const char*",  "dpiScope",        "const char*",
               "%E-mtaskstate", "%E-triggervec", "%E-dly-sched", "%E-trig-sched",   "%E-dyn-sched",
               "%E-fork",       "IData",         "QData",        "%E-logic-implct", " MAX"};
        return names[m_e];
    }
    static void selfTest() {
        UASSERT(0 == std::strcmp(VBasicDTypeKwd{_ENUM_MAX}.ascii(), " MAX"),
                "SelfTest: Enum mismatch");
        UASSERT(0 == std::strcmp(VBasicDTypeKwd{_ENUM_MAX}.dpiType(), " MAX"),
                "SelfTest: Enum mismatch");
    }
    VBasicDTypeKwd()
        : m_e{UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VBasicDTypeKwd(en _e)
        : m_e{_e} {}
    explicit VBasicDTypeKwd(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    int width() const {
        switch (m_e) {
        case BIT: return 1;  // scalar, can't bit extract unless ranged
        case BYTE: return 8;
        case CHANDLE: return 64;
        case EVENT: return 1;
        case INT: return 32;
        case INTEGER: return 32;
        case LOGIC: return 1;  // scalar, can't bit extract unless ranged
        case LONGINT: return 64;
        case DOUBLE: return 64;  // opaque
        case SHORTINT: return 16;
        case TIME: return 64;
        case STRING: return 64;  // opaque  // Just the pointer, for today
        case SCOPEPTR: return 0;  // opaque
        case CHARPTR: return 0;  // opaque
        case MTASKSTATE: return 0;  // opaque
        case TRIGGERVEC: return 0;  // opaque
        case DELAY_SCHEDULER: return 0;  // opaque
        case TRIGGER_SCHEDULER: return 0;  // opaque
        case DYNAMIC_TRIGGER_SCHEDULER: return 0;  // opaque
        case FORK_SYNC: return 0;  // opaque
        case UINT32: return 32;
        case UINT64: return 64;
        default: return 0;
        }
    }
    bool isSigned() const {
        return m_e == BYTE || m_e == SHORTINT || m_e == INT || m_e == LONGINT || m_e == INTEGER
               || m_e == DOUBLE;
    }
    bool isUnsigned() const {
        return m_e == CHANDLE || m_e == EVENT || m_e == STRING || m_e == SCOPEPTR || m_e == CHARPTR
               || m_e == UINT32 || m_e == UINT64 || m_e == BIT || m_e == LOGIC || m_e == TIME;
    }
    bool isFourstate() const {
        return m_e == INTEGER || m_e == LOGIC || m_e == LOGIC_IMPLICIT || m_e == TIME;
    }
    bool isZeroInit() const {  // Otherwise initializes to X
        return (m_e == BIT || m_e == BYTE || m_e == CHANDLE || m_e == EVENT || m_e == INT
                || m_e == LONGINT || m_e == SHORTINT || m_e == STRING || m_e == DOUBLE);
    }
    bool isIntNumeric() const {  // Enum increment supported
        return (m_e == BIT || m_e == BYTE || m_e == INT || m_e == INTEGER || m_e == LOGIC
                || m_e == LONGINT || m_e == SHORTINT || m_e == UINT32 || m_e == UINT64);
    }
    bool isBitLogic() const {  // Bit/logic vector types; can form a packed array
        return (m_e == LOGIC || m_e == BIT);
    }
    bool isDpiUnsignable() const {  // Can add "unsigned" to DPI
        return (m_e == BYTE || m_e == SHORTINT || m_e == INT || m_e == LONGINT || m_e == INTEGER);
    }
    bool isDpiCLayout() const {  // Uses standard C layout, for DPI runtime access
        return (m_e == BIT || m_e == BYTE || m_e == CHANDLE || m_e == INT || m_e == LONGINT
                || m_e == DOUBLE || m_e == SHORTINT || m_e == UINT32 || m_e == UINT64);
    }
    bool isOpaque() const VL_MT_SAFE {  // IE not a simple number we can bit optimize
        return (m_e == EVENT || m_e == STRING || m_e == SCOPEPTR || m_e == CHARPTR
                || m_e == MTASKSTATE || m_e == TRIGGERVEC || m_e == DELAY_SCHEDULER
                || m_e == TRIGGER_SCHEDULER || m_e == DYNAMIC_TRIGGER_SCHEDULER || m_e == FORK_SYNC
                || m_e == DOUBLE);
    }
    bool isDouble() const VL_MT_SAFE { return m_e == DOUBLE; }
    bool isEvent() const { return m_e == EVENT; }
    bool isString() const VL_MT_SAFE { return m_e == STRING; }
    bool isMTaskState() const VL_MT_SAFE { return m_e == MTASKSTATE; }
    // Does this represent a C++ LiteralType? (can be constexpr)
    bool isLiteralType() const VL_MT_SAFE {
        switch (m_e) {
        case BIT:
        case BYTE:
        case CHANDLE:
        case INT:
        case INTEGER:
        case LOGIC:
        case LONGINT:
        case DOUBLE:
        case SHORTINT:
        case SCOPEPTR:
        case CHARPTR:
        case UINT32:
        case UINT64: return true;
        default: return false;
        }
    }
};
constexpr bool operator==(const VBasicDTypeKwd& lhs, const VBasicDTypeKwd& rhs) VL_MT_SAFE {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VBasicDTypeKwd& lhs, VBasicDTypeKwd::en rhs) VL_MT_SAFE {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VBasicDTypeKwd::en lhs, const VBasicDTypeKwd& rhs) VL_MT_SAFE {
    return lhs == rhs.m_e;
}

//######################################################################

class VDirection final {
public:
    enum en : uint8_t { NONE, INPUT, OUTPUT, INOUT, REF, CONSTREF };
    enum en m_e;
    VDirection()
        : m_e{NONE} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VDirection(en _e)
        : m_e{_e} {}
    explicit VDirection(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const VL_MT_SAFE { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"NONE", "INPUT", "OUTPUT", "INOUT", "REF", "CONSTREF"};
        return names[m_e];
    }
    string verilogKwd() const {
        static const char* const names[] = {"", "input", "output", "inout", "ref", "const ref"};
        return names[m_e];
    }
    string xmlKwd() const {  // For historical reasons no "put" suffix
        static const char* const names[] = {"", "in", "out", "inout", "ref", "const ref"};
        return names[m_e];
    }
    string prettyName() const { return verilogKwd(); }
    bool isAny() const { return m_e != NONE; }
    // Looks like inout - "ish" because not identical to being an INOUT
    bool isInoutish() const { return m_e == INOUT; }
    bool isNonOutput() const {
        return m_e == INPUT || m_e == INOUT || m_e == REF || m_e == CONSTREF;
    }
    bool isReadOnly() const VL_MT_SAFE { return m_e == INPUT || m_e == CONSTREF; }
    bool isWritable() const VL_MT_SAFE { return m_e == OUTPUT || m_e == INOUT || m_e == REF; }
    bool isRefOrConstRef() const VL_MT_SAFE { return m_e == REF || m_e == CONSTREF; }
};
constexpr bool operator==(const VDirection& lhs, const VDirection& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VDirection& lhs, VDirection::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VDirection::en lhs, const VDirection& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VDirection& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

/// Boolean or unknown
class VBoolOrUnknown final {
public:
    enum en : uint8_t { BU_FALSE = 0, BU_TRUE = 1, BU_UNKNOWN = 2, _ENUM_END };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    VBoolOrUnknown()
        : m_e{BU_UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VBoolOrUnknown(en _e)
        : m_e{_e} {}
    explicit VBoolOrUnknown(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    const char* ascii() const {
        static const char* const names[] = {"FALSE", "TRUE", "UNK"};
        return names[m_e];
    }
    bool trueKnown() const { return m_e == BU_TRUE; }
    bool trueUnknown() const { return m_e == BU_TRUE || m_e == BU_UNKNOWN; }
    bool falseKnown() const { return m_e == BU_FALSE; }
    bool falseUnknown() const { return m_e == BU_FALSE || m_e == BU_UNKNOWN; }
    bool unknown() const { return m_e == BU_UNKNOWN; }
    void setTrueOrFalse(bool flag) { m_e = flag ? BU_TRUE : BU_FALSE; }
};
constexpr bool operator==(const VBoolOrUnknown& lhs, const VBoolOrUnknown& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VBoolOrUnknown& lhs, VBoolOrUnknown::en rhs) {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VBoolOrUnknown::en lhs, const VBoolOrUnknown& rhs) {
    return lhs == rhs.m_e;
}
inline std::ostream& operator<<(std::ostream& os, const VBoolOrUnknown& rhs) {
    return os << rhs.ascii();
}

//######################################################################

/// Join type
class VJoinType final {
public:
    enum en : uint8_t { JOIN = 0, JOIN_ANY = 1, JOIN_NONE = 2 };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    VJoinType()
        : m_e{JOIN} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VJoinType(en _e)
        : m_e{_e} {}
    explicit VJoinType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    const char* ascii() const {
        static const char* const names[] = {"JOIN", "JOIN_ANY", "JOIN_NONE"};
        return names[m_e];
    }
    const char* verilogKwd() const {
        static const char* const names[] = {"join", "join_any", "join_none"};
        return names[m_e];
    }
    bool join() const { return m_e == JOIN; }
    bool joinAny() const { return m_e == JOIN_ANY; }
    bool joinNone() const { return m_e == JOIN_NONE; }
};
constexpr bool operator==(const VJoinType& lhs, const VJoinType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VJoinType& lhs, VJoinType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VJoinType::en lhs, const VJoinType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VJoinType& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

class VVarType final {
public:
    enum en : uint8_t {
        UNKNOWN,
        GPARAM,
        LPARAM,
        GENVAR,
        VAR,  // Reg, integer, logic, etc
        SUPPLY0,
        SUPPLY1,
        WIRE,
        WREAL,
        IMPLICITWIRE,
        TRIWIRE,
        TRI0,
        TRI1,
        PORT,  // Temp type used in parser only
        BLOCKTEMP,
        MODULETEMP,
        STMTTEMP,
        XTEMP,
        IFACEREF,  // Used to link Interfaces between modules
        MEMBER
    };
    enum en m_e;
    VVarType() VL_MT_SAFE : m_e{UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VVarType(en _e) VL_MT_SAFE : m_e{_e} {}
    explicit VVarType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {
            "?",         "GPARAM",     "LPARAM",       "GENVAR",  "VAR",      "SUPPLY0", "SUPPLY1",
            "WIRE",      "WREAL",      "IMPLICITWIRE", "TRIWIRE", "TRI0",     "TRI1",    "PORT",
            "BLOCKTEMP", "MODULETEMP", "STMTTEMP",     "XTEMP",   "IFACEREF", "MEMBER"};
        return names[m_e];
    }
    bool isSignal() const {
        return (m_e == WIRE || m_e == WREAL || m_e == IMPLICITWIRE || m_e == TRIWIRE || m_e == TRI0
                || m_e == TRI1 || m_e == PORT || m_e == SUPPLY0 || m_e == SUPPLY1 || m_e == VAR);
    }
    bool isNet() const {
        return (m_e == WIRE || m_e == IMPLICITWIRE || m_e == TRIWIRE || m_e == TRI0 || m_e == TRI1
                || m_e == SUPPLY0 || m_e == SUPPLY1);
    }
    bool isContAssignable() const {  // In Verilog, always ok in SystemVerilog
        return (m_e == SUPPLY0 || m_e == SUPPLY1 || m_e == WIRE || m_e == WREAL
                || m_e == IMPLICITWIRE || m_e == TRIWIRE || m_e == TRI0 || m_e == TRI1
                || m_e == PORT || m_e == BLOCKTEMP || m_e == MODULETEMP || m_e == STMTTEMP
                || m_e == XTEMP || m_e == IFACEREF);
    }
    bool isProcAssignable() const {
        return (m_e == GPARAM || m_e == LPARAM || m_e == GENVAR || m_e == VAR || m_e == BLOCKTEMP
                || m_e == MODULETEMP || m_e == STMTTEMP || m_e == XTEMP || m_e == IFACEREF
                || m_e == MEMBER);
    }
    bool isTemp() const {
        return (m_e == BLOCKTEMP || m_e == MODULETEMP || m_e == STMTTEMP || m_e == XTEMP);
    }
};
constexpr bool operator==(const VVarType& lhs, const VVarType& rhs) VL_MT_SAFE {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VVarType& lhs, VVarType::en rhs) VL_MT_SAFE {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VVarType::en lhs, const VVarType& rhs) VL_MT_SAFE {
    return lhs == rhs.m_e;
}
inline std::ostream& operator<<(std::ostream& os, const VVarType& rhs) VL_MT_SAFE {
    return os << rhs.ascii();
}

// ######################################################################

class VBranchPred final {
public:
    enum en : uint8_t { BP_UNKNOWN = 0, BP_LIKELY, BP_UNLIKELY, _ENUM_END };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    VBranchPred()
        : m_e{BP_UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VBranchPred(en _e)
        : m_e{_e} {}
    explicit VBranchPred(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    bool unknown() const { return m_e == BP_UNKNOWN; }
    bool likely() const { return m_e == BP_LIKELY; }
    bool unlikely() const { return m_e == BP_UNLIKELY; }
    VBranchPred invert() const {
        if (m_e == BP_UNLIKELY) {
            return BP_LIKELY;
        } else if (m_e == BP_LIKELY) {
            return BP_UNLIKELY;
        } else {
            return m_e;
        }
    }
    const char* ascii() const {
        static const char* const names[] = {"", "VL_LIKELY", "VL_UNLIKELY"};
        return names[m_e];
    }
};
constexpr bool operator==(const VBranchPred& lhs, const VBranchPred& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VBranchPred& lhs, VBranchPred::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VBranchPred::en lhs, const VBranchPred& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VBranchPred& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

class VVarAttrClocker final {
public:
    enum en : uint8_t { CLOCKER_UNKNOWN = 0, CLOCKER_YES, CLOCKER_NO, _ENUM_END };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    VVarAttrClocker()
        : m_e{CLOCKER_UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VVarAttrClocker(en _e)
        : m_e{_e} {}
    explicit VVarAttrClocker(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    bool unknown() const { return m_e == CLOCKER_UNKNOWN; }
    VVarAttrClocker invert() const {
        if (m_e == CLOCKER_YES) {
            return CLOCKER_NO;
        } else if (m_e == CLOCKER_NO) {
            return CLOCKER_YES;
        } else {
            return m_e;
        }
    }
    const char* ascii() const {
        static const char* const names[] = {"", "clker", "non_clker"};
        return names[m_e];
    }
};
constexpr bool operator==(const VVarAttrClocker& lhs, const VVarAttrClocker& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VVarAttrClocker& lhs, VVarAttrClocker::en rhs) {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VVarAttrClocker::en lhs, const VVarAttrClocker& rhs) {
    return lhs == rhs.m_e;
}
inline std::ostream& operator<<(std::ostream& os, const VVarAttrClocker& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class VAlwaysKwd final {
public:
    enum en : uint8_t { ALWAYS, ALWAYS_FF, ALWAYS_LATCH, ALWAYS_COMB };
    enum en m_e;
    VAlwaysKwd()
        : m_e{ALWAYS} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VAlwaysKwd(en _e)
        : m_e{_e} {}
    explicit VAlwaysKwd(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"always", "always_ff", "always_latch", "always_comb"};
        return names[m_e];
    }
};
constexpr bool operator==(const VAlwaysKwd& lhs, const VAlwaysKwd& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VAlwaysKwd& lhs, VAlwaysKwd::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VAlwaysKwd::en lhs, const VAlwaysKwd& rhs) { return lhs == rhs.m_e; }

// ######################################################################

class VCaseType final {
public:
    enum en : uint8_t { CT_CASE, CT_CASEX, CT_CASEZ, CT_CASEINSIDE };
    enum en m_e;
    VCaseType()
        : m_e{CT_CASE} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VCaseType(en _e)
        : m_e{_e} {}
    explicit VCaseType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
};
constexpr bool operator==(const VCaseType& lhs, const VCaseType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VCaseType& lhs, VCaseType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VCaseType::en lhs, const VCaseType& rhs) { return lhs == rhs.m_e; }

// ######################################################################

class VDisplayType final {
public:
    enum en : uint8_t {
        DT_DISPLAY,
        DT_WRITE,
        DT_MONITOR,
        DT_STROBE,
        DT_INFO,
        DT_ERROR,
        DT_WARNING,
        DT_FATAL
    };
    enum en m_e;
    VDisplayType()
        : m_e{DT_DISPLAY} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VDisplayType(en _e)
        : m_e{_e} {}
    explicit VDisplayType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    bool addNewline() const { return m_e != DT_WRITE; }
    bool needScopeTracking() const { return m_e != DT_DISPLAY && m_e != DT_WRITE; }
    const char* ascii() const {
        static const char* const names[]
            = {"display", "write", "monitor", "strobe", "info", "error", "warning", "fatal"};
        return names[m_e];
    }
};
constexpr bool operator==(const VDisplayType& lhs, const VDisplayType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VDisplayType& lhs, VDisplayType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VDisplayType::en lhs, const VDisplayType& rhs) { return lhs == rhs.m_e; }

// ######################################################################

class VDumpCtlType final {
public:
    enum en : uint8_t { FILE, VARS, ALL, FLUSH, LIMIT, OFF, ON };
    enum en m_e;
    VDumpCtlType()
        : m_e{ON} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VDumpCtlType(en _e)
        : m_e{_e} {}
    explicit VDumpCtlType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"$dumpfile",  "$dumpvars", "$dumpall", "$dumpflush",
                                            "$dumplimit", "$dumpoff",  "$dumpon"};
        return names[m_e];
    }
};
constexpr bool operator==(const VDumpCtlType& lhs, const VDumpCtlType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VDumpCtlType& lhs, VDumpCtlType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VDumpCtlType::en lhs, const VDumpCtlType& rhs) { return lhs == rhs.m_e; }

// ######################################################################

class VParseRefExp final {
public:
    enum en : uint8_t {
        PX_NONE,  // Used in V3LinkParse only
        PX_ROOT,
        PX_TEXT  // Unknown ID component
    };
    enum en m_e;
    VParseRefExp()
        : m_e{PX_NONE} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VParseRefExp(en _e)
        : m_e{_e} {}
    explicit VParseRefExp(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"", "$root", "TEXT", "PREDOT"};
        return names[m_e];
    }
};
constexpr bool operator==(const VParseRefExp& lhs, const VParseRefExp& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VParseRefExp& lhs, VParseRefExp::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VParseRefExp::en lhs, const VParseRefExp& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VParseRefExp& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

class VStrength final {
public:
    enum en : uint8_t { HIGHZ, SMALL, MEDIUM, WEAK, LARGE, PULL, STRONG, SUPPLY };
    enum en m_e;

    // cppcheck-suppress noExplicitConstructor
    constexpr VStrength(en strengthLevel)
        : m_e(strengthLevel) {}
    explicit VStrength(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[]
            = {"highz", "small", "medium", "weak", "large", "pull", "strong", "supply"};
        return names[m_e];
    }
};
constexpr bool operator==(const VStrength& lhs, const VStrength& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VStrength& lhs, VStrength::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VStrength::en lhs, const VStrength& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VStrength& rhs) {
    return os << rhs.ascii();
}

// ######################################################################
//  VNumRange - Structure containing numeric range information
//  See also AstRange, which is a symbolic version of this

class VNumRange final {
public:
    int m_left = 0;
    int m_right = 0;
    bool m_ranged = false;  // Has a range
    bool operator==(const VNumRange& rhs) const {
        return m_left == rhs.m_left && m_right == rhs.m_right && m_ranged == rhs.m_ranged;
    }
    bool operator<(const VNumRange& rhs) const {
        if ((m_left < rhs.m_left)) return true;
        if (!(m_left == rhs.m_left)) return false;  // lhs > rhs
        if ((m_right < rhs.m_right)) return true;
        if (!(m_right == rhs.m_right)) return false;  // lhs > rhs
        if ((m_ranged < rhs.m_ranged)) return true;
        if (!(m_ranged == rhs.m_ranged)) return false;  // lhs > rhs
        return false;
    }
    //
    VNumRange() = default;
    VNumRange(int hi, int lo, bool littleEndian) { init(hi, lo, littleEndian); }
    VNumRange(int left, int right)
        : m_left{left}
        , m_right{right}
        , m_ranged{true} {}
    ~VNumRange() = default;
    // MEMBERS
    void init(int hi, int lo, bool littleEndian) {
        if (lo > hi) {
            const int t = hi;
            hi = lo;
            lo = t;
        }
        m_left = littleEndian ? lo : hi;
        m_right = littleEndian ? hi : lo;
        m_ranged = true;
    }
    int left() const { return m_left; }
    int right() const { return m_right; }
    int hi() const VL_MT_SAFE {
        return m_left > m_right ? m_left : m_right;
    }  // How to show a declaration
    int lo() const VL_MT_SAFE {
        return m_left > m_right ? m_right : m_left;
    }  // How to show a declaration
    int leftToRightInc() const { return littleEndian() ? 1 : -1; }
    int elements() const VL_MT_SAFE { return hi() - lo() + 1; }
    bool ranged() const { return m_ranged; }
    bool littleEndian() const { return m_left < m_right; }
    int hiMaxSelect() const {
        return (lo() < 0 ? hi() - lo() : hi());
    }  // Maximum value a [] select may index
    void dump(std::ostream& str) const {
        if (ranged()) {
            str << "[" << left() << ":" << right() << "]";
        } else {
            str << "[norg]";
        }
    }
};
inline std::ostream& operator<<(std::ostream& os, const VNumRange& rhs) {
    rhs.dump(os);
    return os;
}

//######################################################################

class VUseType final {
public:
    enum en : uint8_t {
        IMP_INCLUDE,  // Implementation (.cpp) needs an include
        INT_INCLUDE,  // Interface (.h) needs an include
        IMP_FWD_CLASS,  // Implementation (.cpp) needs a forward class declaration
        INT_FWD_CLASS,  // Interface (.h) needs a forward class declaration
    };
    enum en m_e;
    VUseType()
        : m_e{IMP_FWD_CLASS} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VUseType(en _e)
        : m_e{_e} {}
    explicit VUseType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    bool isInclude() const { return m_e == IMP_INCLUDE || m_e == INT_INCLUDE; }
    bool isFwdClass() const { return m_e == IMP_FWD_CLASS || m_e == INT_FWD_CLASS; }
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"IMP_INC", "INT_INC", "IMP_FWD", "INT_FWD"};
        return names[m_e];
    }
};
constexpr bool operator==(const VUseType& lhs, const VUseType& rhs) { return lhs.m_e == rhs.m_e; }
constexpr bool operator==(const VUseType& lhs, VUseType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VUseType::en lhs, const VUseType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VUseType& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

class VBasicTypeKey final {
public:
    const int m_width;  // From AstNodeDType: Bit width of operation
    const int m_widthMin;  // From AstNodeDType: If unsized, bitwidth of minimum implementation
    const VSigning m_numeric;  // From AstNodeDType: Node is signed
    const VBasicDTypeKwd m_keyword;  // From AstBasicDType: What keyword created basic type
    const VNumRange m_nrange;  // From AstBasicDType: Numeric msb/lsb (if non-opaque keyword)
    bool operator==(const VBasicTypeKey& rhs) const {
        return m_width == rhs.m_width && m_widthMin == rhs.m_widthMin && m_numeric == rhs.m_numeric
               && m_keyword == rhs.m_keyword && m_nrange == rhs.m_nrange;
    }
    bool operator<(const VBasicTypeKey& rhs) const {
        if ((m_width < rhs.m_width)) return true;
        if (!(m_width == rhs.m_width)) return false;  // lhs > rhs
        if ((m_widthMin < rhs.m_widthMin)) return true;
        if (!(m_widthMin == rhs.m_widthMin)) return false;  // lhs > rhs
        if ((m_numeric < rhs.m_numeric)) return true;
        if (!(m_numeric == rhs.m_numeric)) return false;  // lhs > rhs
        if ((m_keyword < rhs.m_keyword)) return true;
        if (!(m_keyword == rhs.m_keyword)) return false;  // lhs > rhs
        if ((m_nrange < rhs.m_nrange)) return true;
        if (!(m_nrange == rhs.m_nrange)) return false;  // lhs > rhs
        return false;
    }
    VBasicTypeKey(int width, int widthMin, VSigning numeric, VBasicDTypeKwd kwd,
                  const VNumRange& nrange)
        : m_width{width}
        , m_widthMin{widthMin}
        , m_numeric{numeric}
        , m_keyword{kwd}
        , m_nrange{nrange} {}
    ~VBasicTypeKey() = default;
};

//######################################################################
// AstNUser - Generic base class for AST User nodes.
//          - Also used to allow parameter passing up/down iterate calls

class WidthVP;
class V3GraphVertex;
class VSymEnt;

class VNUser final {
    union {
        void* up;
        int ui;
    } m_u;

public:
    VNUser() = default;
    // non-explicit:
    // cppcheck-suppress noExplicitConstructor
    VNUser(int i) {
        m_u.up = 0;
        m_u.ui = i;
    }
    explicit VNUser(void* p) { m_u.up = p; }
    ~VNUser() = default;
    // Casters
    template <class T>
    typename std::enable_if<std::is_pointer<T>::value, T>::type to() const VL_MT_SAFE {
        return reinterpret_cast<T>(m_u.up);
    }
    WidthVP* c() const { return to<WidthVP*>(); }
    VSymEnt* toSymEnt() const { return to<VSymEnt*>(); }
    AstNode* toNodep() const VL_MT_SAFE { return to<AstNode*>(); }
    V3GraphVertex* toGraphVertex() const { return to<V3GraphVertex*>(); }
    int toInt() const { return m_u.ui; }
    static VNUser fromInt(int i) { return VNUser{i}; }
};

//######################################################################
// AstUserResource - Generic pointer base class for tracking usage of user()
//
//  Where AstNode->user2() is going to be used, for example, you write:
//
//      VNUser2InUse  m_userres;
//
//  This will clear the tree, and prevent another visitor from clobbering
//  user2.  When the member goes out of scope it will be automagically
//  freed up.

class VNUserInUseBase VL_NOT_FINAL {
protected:
    static void allocate(int id, uint32_t& cntGblRef, bool& userBusyRef) {
        // Perhaps there's still a AstUserInUse in scope for this?
        UASSERT_STATIC(!userBusyRef, "Conflicting user use; AstUser" + cvtToStr(id)
                                         + "InUse request when under another AstUserInUse");
        userBusyRef = true;
        clearcnt(id, cntGblRef, userBusyRef);
    }
    static void free(int id, uint32_t& cntGblRef, bool& userBusyRef) {
        UASSERT_STATIC(userBusyRef, "Free of User" + cvtToStr(id) + "() not under AstUserInUse");
        clearcnt(id, cntGblRef, userBusyRef);  // Includes a checkUse for us
        userBusyRef = false;
    }
    static void clearcnt(int id, uint32_t& cntGblRef, const bool& userBusyRef) {
        UASSERT_STATIC(userBusyRef, "Clear of User" + cvtToStr(id) + "() not under AstUserInUse");
        // If this really fires and is real (after 2^32 edits???)
        // we could just walk the tree and clear manually
        ++cntGblRef;
        UASSERT_STATIC(cntGblRef, "User*() overflowed!");
    }
    static void checkcnt(int id, uint32_t&, const bool& userBusyRef) {
        UASSERT_STATIC(userBusyRef,
                       "Check of User" + cvtToStr(id) + "() failed, not under AstUserInUse");
    }
};

// For each user() declare the in use structure
// We let AstNode peek into here, because when under low optimization even
// an accessor would be way too slow.
// clang-format off
class VNUser1InUse final : VNUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    VNUser1InUse()     { allocate(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser1InUse()    { free    (1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class VNUser2InUse final : VNUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    VNUser2InUse()     { allocate(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser2InUse()    { free    (2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class VNUser3InUse final : VNUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    VNUser3InUse()     { allocate(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser3InUse()    { free    (3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class VNUser4InUse final : VNUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    VNUser4InUse()     { allocate(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser4InUse()    { free    (4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class VNUser5InUse final : VNUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    VNUser5InUse()     { allocate(5, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser5InUse()    { free    (5, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(5, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(5, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
// clang-format on

//######################################################################
// Node deleter, deletes all enqueued AstNode* on destruction, or when
// explicitly told to do so. This is useful when the deletion of removed
// nodes needs to be deferred to a later time, because pointers to the
// removed nodes might still exist.

class VNDeleter VL_NOT_FINAL {
    // MEMBERS
    std::vector<AstNode*> m_deleteps;  // Nodes to delete

public:
    // METHODS

    // Enqueue node for deletion on next 'doDelete' (or destruction)
    void pushDeletep(AstNode* nodep) {
        UASSERT_STATIC(nodep, "Cannot delete nullptr node");
        m_deleteps.push_back(nodep);
    }

    // Delete all previously pushed nodes (by callint deleteTree)
    void doDeletes();

    // Do the deletions on destruction
    virtual ~VNDeleter() { doDeletes(); }
};

//######################################################################
// VNVisitor -- Allows new functions to be called on each node
// type without changing the base classes.  See "Modern C++ Design".

class VNVisitor VL_NOT_FINAL : public VNDeleter {
    friend class AstNode;

public:
    /// Call visit()s on nodep
    inline void iterate(AstNode* nodep);
    /// Call visit()s on nodep
    inline void iterateNull(AstNode* nodep);
    /// Call visit()s on nodep's children
    inline void iterateChildren(AstNode* nodep);
    /// Call visit()s on nodep's children in backp() order
    inline void iterateChildrenBackwards(AstNode* nodep);
    /// Call visit()s on const nodep's children
    inline void iterateChildrenConst(AstNode* nodep);
    /// Call visit()s on nodep (maybe nullptr) and nodep's nextp() list
    inline void iterateAndNextNull(AstNode* nodep);
    /// Call visit()s on const nodep (maybe nullptr) and nodep's nextp() list
    inline void iterateAndNextConstNull(AstNode* nodep);
    /// Call visit()s on const nodep (maybe nullptr) and nodep's nextp() list, in reverse order
    inline void iterateAndNextConstNullBackwards(AstNode* nodep);
    /// Return edited nodep; see comments in V3Ast.cpp
    inline AstNode* iterateSubtreeReturnEdits(AstNode* nodep);

    virtual void visit(AstNode* nodep) = 0;
#include "V3Ast__gen_visitor_decls.h"  // From ./astgen
};

//######################################################################
// VNRelinker -- Holds the state of a unlink so a new node can be
// added at the same point.

class VNRelinker final {
protected:
    friend class AstNode;
    enum RelinkWhatEn : uint8_t {
        RELINK_BAD,
        RELINK_NEXT,
        RELINK_OP1,
        RELINK_OP2,
        RELINK_OP3,
        RELINK_OP4
    };
    AstNode* m_oldp = nullptr;  // The old node that was linked to this point in the tree
    AstNode* m_backp = nullptr;
    RelinkWhatEn m_chg = RELINK_BAD;
    AstNode** m_iterpp = nullptr;

public:
    VNRelinker() = default;
    inline void relink(AstNode* newp);
    AstNode* oldp() const { return m_oldp; }
    void dump(std::ostream& str = std::cout) const;
};
inline std::ostream& operator<<(std::ostream& os, const VNRelinker& rhs) {
    rhs.dump(os);
    return os;
}

// ######################################################################
//  Callback base class to determine if node matches some formula

class VNodeMatcher VL_NOT_FINAL {
public:
    virtual bool nodeMatch(const AstNode* nodep) const { return true; }
};

// ######################################################################
//   AstNode -- Base type of all Ast types

// Prefetch a node.
#define ASTNODE_PREFETCH_NON_NULL(nodep) \
    do { \
        VL_PREFETCH_RD(&((nodep)->m_nextp)); \
        VL_PREFETCH_RD(&((nodep)->m_type)); \
    } while (false)
// The if() makes it faster, even though prefetch won't fault on null pointers
#define ASTNODE_PREFETCH(nodep) \
    do { \
        if (nodep) ASTNODE_PREFETCH_NON_NULL(nodep); \
    } while (false)

class AstNode VL_NOT_FINAL {
    // v ASTNODE_PREFETCH depends on below ordering of members
    AstNode* m_nextp = nullptr;  // Next peer in the parent's list
    AstNode* m_backp = nullptr;  // Node that points to this one (via next/op1/op2/...)
    AstNode* m_op1p = nullptr;  // Generic pointer 1
    AstNode* m_op2p = nullptr;  // Generic pointer 2
    AstNode* m_op3p = nullptr;  // Generic pointer 3
    AstNode* m_op4p = nullptr;  // Generic pointer 4
    AstNode** m_iterpp
        = nullptr;  // Pointer to node iterating on, change it if we replace this node.
    const VNType m_type;  // Node sub-type identifier
    // ^ ASTNODE_PREFETCH depends on above ordering of members

    // VNType is 2 bytes, so we can stick another 6 bytes after it to utilize what would
    // otherwise be padding (on a 64-bit system). We stick the attribute flags, broken state,
    // and the clone count here.

    struct {
        bool didWidth : 1;  // Did V3Width computation
        bool doingWidth : 1;  // Inside V3Width
        bool protect : 1;  // Protect name if protection is on
        // Space for more flags here (there must be 8 bits in total)
        uint8_t unused : 5;
    } m_flags;  // Attribute flags

    // State variable used by V3Broken for consistency checking. The top bit of this is byte is a
    // flag, representing V3Broken is currently proceeding under this node. The bottom 7 bits are
    // a generation number. This is hot when --debug-checks so we access as a whole to avoid bit
    // field masking resulting in unnecessary read-modify-write ops.
    uint8_t m_brokenState = 0;

    int m_cloneCnt = 0;  // Sequence number for when last clone was made

#if defined(__x86_64__) && defined(__gnu_linux__)
    // Only assert this on known platforms, as it only affects performance, not correctness
    static_assert(sizeof(m_type) + sizeof(m_flags) + sizeof(m_brokenState) + sizeof(m_cloneCnt)
                      <= sizeof(void*),
                  "packing requires padding");
#endif

    AstNodeDType* m_dtypep = nullptr;  // Data type of output or assignment (etc)
    AstNode* m_headtailp;  // When at begin/end of list, the opposite end of the list
    FileLine* m_fileline;  // Where it was declared
#ifdef VL_DEBUG
    // Only keep track of the edit count in the node in the debug build.
    // In the release build we will take the space saving instead.
    uint64_t m_editCount;  // When it was last edited
#endif
    static uint64_t s_editCntGbl;  // Global edit counter
    static uint64_t s_editCntLast;  // Last committed value of global edit counter

    AstNode* m_clonep = nullptr;  // Pointer to clone/source of node (only for *LAST* cloneTree())
    static int s_cloneCntGbl;  // Count of which userp is set

    // This member ordering both allows 64 bit alignment and puts associated data together
    VNUser m_user1u{0};  // Contains any information the user iteration routine wants
    uint32_t m_user1Cnt = 0;  // Mark of when userp was set
    uint32_t m_user2Cnt = 0;  // Mark of when userp was set
    VNUser m_user2u{0};  // Contains any information the user iteration routine wants
    VNUser m_user3u{0};  // Contains any information the user iteration routine wants
    uint32_t m_user3Cnt = 0;  // Mark of when userp was set
    uint32_t m_user4Cnt = 0;  // Mark of when userp was set
    VNUser m_user4u{0};  // Contains any information the user iteration routine wants
    VNUser m_user5u{0};  // Contains any information the user iteration routine wants
    uint32_t m_user5Cnt = 0;  // Mark of when userp was set

    // METHODS
    void op1p(AstNode* nodep) {
        m_op1p = nodep;
        if (nodep) nodep->m_backp = this;
    }
    void op2p(AstNode* nodep) {
        m_op2p = nodep;
        if (nodep) nodep->m_backp = this;
    }
    void op3p(AstNode* nodep) {
        m_op3p = nodep;
        if (nodep) nodep->m_backp = this;
    }
    void op4p(AstNode* nodep) {
        m_op4p = nodep;
        if (nodep) nodep->m_backp = this;
    }

private:
    AstNode* cloneTreeIter();
    AstNode* cloneTreeIterList();
    void checkTreeIter(const AstNode* backp) const VL_MT_SAFE;
    bool gateTreeIter() const;
    static bool sameTreeIter(const AstNode* node1p, const AstNode* node2p, bool ignNext,
                             bool gateOnly);
    void deleteTreeIter();
    void deleteNode();
    string instanceStr() const;

public:
    static void relinkOneLink(AstNode*& pointpr, AstNode* newp);
    // cppcheck-suppress functionConst
    static void debugTreeChange(const AstNode* nodep, const char* prefix, int lineno, bool next);

protected:
    // CONSTRUCTORS
    AstNode(VNType t, FileLine* fl);
    virtual AstNode* clone() = 0;  // Generally, cloneTree is what you want instead
    virtual void cloneRelink() {}
    void cloneRelinkTree();

    // METHODS
    void setOp1p(AstNode* newp);  // Set non-list-type op1 to non-list element
    void setOp2p(AstNode* newp);  // Set non-list-type op2 to non-list element
    void setOp3p(AstNode* newp);  // Set non-list-type op3 to non-list element
    void setOp4p(AstNode* newp);  // Set non-list-type op4 to non-list element

    void addOp1p(AstNode* newp);  // Append newp to end of op1
    void addOp2p(AstNode* newp);  // Append newp to end of op2
    void addOp3p(AstNode* newp);  // Append newp to end of op3
    void addOp4p(AstNode* newp);  // Append newp to end of op4

    // clang-format off
    void setNOp1p(AstNode* newp) { if (newp) setOp1p(newp); }
    void setNOp2p(AstNode* newp) { if (newp) setOp2p(newp); }
    void setNOp3p(AstNode* newp) { if (newp) setOp3p(newp); }
    void setNOp4p(AstNode* newp) { if (newp) setOp4p(newp); }

    void addNOp1p(AstNode* newp) { if (newp) addOp1p(newp); }
    void addNOp2p(AstNode* newp) { if (newp) addOp2p(newp); }
    void addNOp3p(AstNode* newp) { if (newp) addOp3p(newp); }
    void addNOp4p(AstNode* newp) { if (newp) addOp4p(newp); }
    // clang-format on

    void clonep(AstNode* nodep) {
        m_clonep = nodep;
        m_cloneCnt = s_cloneCntGbl;
    }
    static void cloneClearTree() {
        s_cloneCntGbl++;
        UASSERT_STATIC(s_cloneCntGbl, "Rollover");
    }

public:
    // ACCESSORS
    VNType type() const VL_MT_SAFE { return m_type; }
    const char* typeName() const VL_MT_SAFE { return type().ascii(); }  // See also prettyTypeName
    AstNode* nextp() const VL_MT_SAFE { return m_nextp; }
    AstNode* backp() const VL_MT_SAFE { return m_backp; }
    AstNode* abovep() const;  // Parent node above, only when no nextp() as otherwise slow
    AstNode* op1p() const VL_MT_SAFE { return m_op1p; }
    AstNode* op2p() const VL_MT_SAFE { return m_op2p; }
    AstNode* op3p() const VL_MT_SAFE { return m_op3p; }
    AstNode* op4p() const VL_MT_SAFE { return m_op4p; }
    AstNodeDType* dtypep() const VL_MT_SAFE { return m_dtypep; }
    AstNode* clonep() const { return ((m_cloneCnt == s_cloneCntGbl) ? m_clonep : nullptr); }
    AstNode* firstAbovep() const {  // Returns nullptr when second or later in list
        return ((backp() && backp()->nextp() != this) ? backp() : nullptr);
    }
    // isFirstInMyListOfStatements(n) -- implemented by child classes:
    // AstNodeBlock, AstCaseItem, AstNodeIf, AstNodeFTask, and possibly others.
    virtual bool isFirstInMyListOfStatements(AstNode* n) const { return false; }
    // isStandaloneBodyStmt == Do we need a ; on generated cpp for this node?
    bool isStandaloneBodyStmt() {
        return (!firstAbovep()  // we're 2nd or later in the list, so yes need ;

                // If we're first in the list, check what backp() thinks of us:
                || (backp() && backp()->isFirstInMyListOfStatements(this)));
    }
    uint8_t brokenState() const VL_MT_SAFE { return m_brokenState; }
    void brokenState(uint8_t value) { m_brokenState = value; }

    // Used by AstNode::broken()
    bool brokeExists() const { return V3Broken::isLinkable(this); }
    bool brokeExistsAbove() const { return brokeExists() && (m_brokenState >> 7); }
    bool brokeExistsBelow() const { return brokeExists() && !(m_brokenState >> 7); }
    // Note: brokeExistsBelow is not quite precise, as it is true for sibling nodes as well

    // CONSTRUCTORS
    virtual ~AstNode() = default;
#ifdef VL_LEAK_CHECKS
    static void* operator new(size_t size);
    static void operator delete(void* obj, size_t size);
#endif

    // CONSTANTS
    // The following are relative dynamic costs (~ execution cycle count) of various operations.
    // They are used by V3InstCount to estimate the relative execution time of code fragments.
    static constexpr int INSTR_COUNT_BRANCH = 4;  // Branch
    static constexpr int INSTR_COUNT_CALL = INSTR_COUNT_BRANCH + 10;  // Subroutine call
    static constexpr int INSTR_COUNT_LD = 2;  // Load memory
    static constexpr int INSTR_COUNT_INT_MUL = 3;  // Integer multiply
    static constexpr int INSTR_COUNT_INT_DIV = 10;  // Integer divide
    static constexpr int INSTR_COUNT_DBL = 8;  // Convert or do float ops
    static constexpr int INSTR_COUNT_DBL_DIV = 40;  // Double divide
    static constexpr int INSTR_COUNT_DBL_TRIG = 200;  // Double trigonometric ops
    static constexpr int INSTR_COUNT_STR = 100;  // String ops
    static constexpr int INSTR_COUNT_TIME = INSTR_COUNT_CALL + 5;  // Determine simulation time
    static constexpr int INSTR_COUNT_PLI = 20;  // PLI routines

    // ACCESSORS
    virtual string name() const VL_MT_SAFE { return ""; }
    virtual string origName() const { return ""; }
    virtual void name(const string& name) {
        this->v3fatalSrc("name() called on object without name() method");
    }
    virtual void tag(const string& text) {}
    virtual string tag() const { return ""; }
    virtual string verilogKwd() const { return ""; }
    string nameProtect() const VL_MT_SAFE;  // Name with --protect-id applied
    string origNameProtect() const;  // origName with --protect-id applied
    string shortName() const;  // Name with __PVT__ removed for concatenating scopes
    static string dedotName(const string& namein);  // Name with dots removed
    static string prettyName(const string& namein);  // Name for printing out to the user
    static string prettyNameQ(const string& namein) {  // Quoted pretty name (for errors)
        return std::string{"'"} + prettyName(namein) + "'";
    }
    static string
    encodeName(const string& namein);  // Encode user name into internal C representation
    static string encodeNumber(int64_t num);  // Encode number into internal C representation
    static string vcdName(const string& namein);  // Name for printing out to vcd files
    string prettyName() const VL_MT_SAFE { return prettyName(name()); }
    string prettyNameQ() const { return prettyNameQ(name()); }
    string prettyTypeName() const;  // "VARREF" for error messages (NOT dtype's pretty name)
    virtual string prettyOperatorName() const { return "operator " + prettyTypeName(); }
    FileLine* fileline() const VL_MT_SAFE { return m_fileline; }
    void fileline(FileLine* fl) { m_fileline = fl; }
    inline bool width1() const;
    inline int widthInstrs() const;
    void didWidth(bool flag) { m_flags.didWidth = flag; }
    bool didWidth() const { return m_flags.didWidth; }
    bool didWidthAndSet() {
        if (didWidth()) return true;
        didWidth(true);
        return false;
    }
    bool doingWidth() const { return m_flags.doingWidth; }
    void doingWidth(bool flag) { m_flags.doingWidth = flag; }
    bool protect() const VL_MT_SAFE { return m_flags.protect; }
    void protect(bool flag) { m_flags.protect = flag; }

    // TODO stomp these width functions out, and call via dtypep() instead
    inline int width() const VL_MT_SAFE;
    inline int widthMin() const;
    int widthMinV() const {
        return v3Global.widthMinUsage() == VWidthMinUsage::VERILOG_WIDTH ? widthMin() : width();
    }
    int widthWords() const { return VL_WORDS_I(width()); }
    bool isQuad() const VL_MT_SAFE { return (width() > VL_IDATASIZE && width() <= VL_QUADSIZE); }
    bool isWide() const VL_MT_SAFE { return (width() > VL_QUADSIZE); }
    inline bool isDouble() const;
    inline bool isSigned() const;
    inline bool isString() const;

    // clang-format off
    VNUser      user1u() const VL_MT_SAFE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser1InUse::s_userBusy, "userp set w/o busy");
        return ((m_user1Cnt==VNUser1InUse::s_userCntGbl) ? m_user1u : VNUser{0});
    }
    AstNode*    user1p() const VL_MT_SAFE { return user1u().toNodep(); }
    void        user1u(const VNUser& user) { m_user1u=user; m_user1Cnt=VNUser1InUse::s_userCntGbl; }
    void        user1p(void* userp) { user1u(VNUser{userp}); }
    int         user1() const { return user1u().toInt(); }
    void        user1(int val) { user1u(VNUser{val}); }
    int         user1Inc(int val=1) { int v=user1(); user1(v+val); return v; }
    int         user1SetOnce() { int v=user1(); if (!v) user1(1); return v; }  // Better for cache than user1Inc()
    static void user1ClearTree() { VNUser1InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser      user2u() const VL_MT_SAFE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser2InUse::s_userBusy, "userp set w/o busy");
        return ((m_user2Cnt==VNUser2InUse::s_userCntGbl) ? m_user2u : VNUser{0});
    }
    AstNode*    user2p() const VL_MT_SAFE { return user2u().toNodep(); }
    void        user2u(const VNUser& user) { m_user2u=user; m_user2Cnt=VNUser2InUse::s_userCntGbl; }
    void        user2p(void* userp) { user2u(VNUser{userp}); }
    int         user2() const { return user2u().toInt(); }
    void        user2(int val) { user2u(VNUser{val}); }
    int         user2Inc(int val=1) { int v=user2(); user2(v+val); return v; }
    int         user2SetOnce() { int v=user2(); if (!v) user2(1); return v; }  // Better for cache than user2Inc()
    static void user2ClearTree() { VNUser2InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser      user3u() const VL_MT_SAFE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser3InUse::s_userBusy, "userp set w/o busy");
        return ((m_user3Cnt==VNUser3InUse::s_userCntGbl) ? m_user3u : VNUser{0});
    }
    AstNode*    user3p() const VL_MT_SAFE { return user3u().toNodep(); }
    void        user3u(const VNUser& user) { m_user3u=user; m_user3Cnt=VNUser3InUse::s_userCntGbl; }
    void        user3p(void* userp) { user3u(VNUser{userp}); }
    int         user3() const { return user3u().toInt(); }
    void        user3(int val) { user3u(VNUser{val}); }
    int         user3Inc(int val=1) { int v=user3(); user3(v+val); return v; }
    int         user3SetOnce() { int v=user3(); if (!v) user3(1); return v; }  // Better for cache than user3Inc()
    static void user3ClearTree() { VNUser3InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser      user4u() const VL_MT_SAFE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser4InUse::s_userBusy, "userp set w/o busy");
        return ((m_user4Cnt==VNUser4InUse::s_userCntGbl) ? m_user4u : VNUser{0});
    }
    AstNode*    user4p() const VL_MT_SAFE { return user4u().toNodep(); }
    void        user4u(const VNUser& user) { m_user4u=user; m_user4Cnt=VNUser4InUse::s_userCntGbl; }
    void        user4p(void* userp) { user4u(VNUser{userp}); }
    int         user4() const { return user4u().toInt(); }
    void        user4(int val) { user4u(VNUser{val}); }
    int         user4Inc(int val=1) { int v=user4(); user4(v+val); return v; }
    int         user4SetOnce() { int v=user4(); if (!v) user4(1); return v; }  // Better for cache than user4Inc()
    static void user4ClearTree() { VNUser4InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser      user5u() const VL_MT_SAFE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser5InUse::s_userBusy, "userp set w/o busy");
        return ((m_user5Cnt==VNUser5InUse::s_userCntGbl) ? m_user5u : VNUser{0});
    }
    AstNode*    user5p() const VL_MT_SAFE { return user5u().toNodep(); }
    void        user5u(const VNUser& user) { m_user5u=user; m_user5Cnt=VNUser5InUse::s_userCntGbl; }
    void        user5p(void* userp) { user5u(VNUser{userp}); }
    int         user5() const { return user5u().toInt(); }
    void        user5(int val) { user5u(VNUser{val}); }
    int         user5Inc(int val=1) { int v=user5(); user5(v+val); return v; }
    int         user5SetOnce() { int v=user5(); if (!v) user5(1); return v; }  // Better for cache than user5Inc()
    static void user5ClearTree() { VNUser5InUse::clear(); }  // Clear userp()'s across the entire tree
    // clang-format on

#ifdef VL_DEBUG
    uint64_t editCount() const { return m_editCount; }
    void editCountInc() {
        m_editCount = ++s_editCntGbl;  // Preincrement, so can "watch AstNode::s_editCntGbl=##"
    }
#else
    void editCountInc() { ++s_editCntGbl; }
#endif
    static uint64_t editCountLast() VL_MT_SAFE { return s_editCntLast; }
    static uint64_t editCountGbl() VL_MT_SAFE { return s_editCntGbl; }
    static void editCountSetLast() { s_editCntLast = editCountGbl(); }

    // ACCESSORS for specific types
    // Alas these can't be virtual or they break when passed a nullptr
    inline bool isZero() const;
    inline bool isOne() const;
    inline bool isNeqZero() const;
    inline bool isAllOnes() const;
    inline bool isAllOnesV() const;  // Verilog width rules apply

    // METHODS - data type changes especially for initial creation
    void dtypep(AstNodeDType* nodep) {
        if (m_dtypep != nodep) {
            m_dtypep = nodep;
            editCountInc();
        }
    }
    void dtypeFrom(const AstNode* fromp) {
        if (fromp) dtypep(fromp->dtypep());
    }
    void dtypeChgSigned(bool flag = true);
    void dtypeChgWidth(int width, int widthMin);
    void dtypeChgWidthSigned(int width, int widthMin, VSigning numeric);
    void dtypeSetBitUnsized(int width, int widthMin, VSigning numeric) {
        dtypep(findBitDType(width, widthMin, numeric));
    }
    void dtypeSetBitSized(int width, VSigning numeric) {
        dtypep(findBitDType(width, width, numeric));  // Since sized, widthMin is width
    }
    void dtypeSetLogicUnsized(int width, int widthMin, VSigning numeric) {
        dtypep(findLogicDType(width, widthMin, numeric));
    }
    void dtypeSetLogicSized(int width, VSigning numeric) {
        dtypep(findLogicDType(width, width, numeric));  // Since sized, widthMin is width
    }
    void dtypeSetBit() { dtypep(findBitDType()); }
    void dtypeSetDouble() { dtypep(findDoubleDType()); }
    void dtypeSetString() { dtypep(findStringDType()); }
    void dtypeSetSigned32() { dtypep(findSigned32DType()); }
    void dtypeSetUInt32() { dtypep(findUInt32DType()); }  // Twostate
    void dtypeSetUInt64() { dtypep(findUInt64DType()); }  // Twostate
    void dtypeSetEmptyQueue() { dtypep(findEmptyQueueDType()); }
    void dtypeSetVoid() { dtypep(findVoidDType()); }

    // Data type locators
    AstNodeDType* findBitDType() const { return findBasicDType(VBasicDTypeKwd::LOGIC); }
    AstNodeDType* findDoubleDType() const { return findBasicDType(VBasicDTypeKwd::DOUBLE); }
    AstNodeDType* findStringDType() const { return findBasicDType(VBasicDTypeKwd::STRING); }
    AstNodeDType* findSigned32DType() const { return findBasicDType(VBasicDTypeKwd::INTEGER); }
    AstNodeDType* findUInt32DType() const { return findBasicDType(VBasicDTypeKwd::UINT32); }
    AstNodeDType* findUInt64DType() const { return findBasicDType(VBasicDTypeKwd::UINT64); }
    AstNodeDType* findCHandleDType() const { return findBasicDType(VBasicDTypeKwd::CHANDLE); }
    AstNodeDType* findEmptyQueueDType() const;
    AstNodeDType* findVoidDType() const;
    AstNodeDType* findQueueIndexDType() const;
    AstNodeDType* findBitDType(int width, int widthMin, VSigning numeric) const;
    AstNodeDType* findLogicDType(int width, int widthMin, VSigning numeric) const;
    AstNodeDType* findLogicRangeDType(const VNumRange& range, int widthMin,
                                      VSigning numeric) const;
    AstNodeDType* findBitRangeDType(const VNumRange& range, int widthMin, VSigning numeric) const;
    AstNodeDType* findBasicDType(VBasicDTypeKwd kwd) const;
    static AstBasicDType* findInsertSameDType(AstBasicDType* nodep);

    // METHODS - dump and error
    void v3errorEnd(std::ostringstream& str) const VL_MT_SAFE;
    void v3errorEndFatal(std::ostringstream& str) const VL_ATTR_NORETURN VL_MT_SAFE;
    string warnContextPrimary() const { return fileline()->warnContextPrimary(); }
    string warnContextSecondary() const { return fileline()->warnContextSecondary(); }
    string warnMore() const { return fileline()->warnMore(); }
    string warnOther() const { return fileline()->warnOther(); }

    virtual void dump(std::ostream& str = std::cout) const;
    static void dumpGdb(const AstNode* nodep);  // For GDB only
    void dumpGdbHeader() const;

    // METHODS - Tree modifications
    // Returns nodep, adds newp to end of nodep's list
    template <typename T_NodeResult, typename T_NodeNext>
    static T_NodeResult* addNext(T_NodeResult* nodep, T_NodeNext* newp) {
        static_assert(std::is_base_of<AstNode, T_NodeResult>::value,
                      "'T_NodeResult' must be a subtype of AstNode");
        static_assert(std::is_base_of<T_NodeResult, T_NodeNext>::value,
                      "'T_NodeNext' must be a subtype of 'T_NodeResult'");
        return static_cast<T_NodeResult*>(addNext<AstNode, AstNode>(nodep, newp));
    }
    inline AstNode* addNext(AstNode* newp);
    inline void addPrev(AstNode* newp);
    void addNextHere(AstNode* newp);  // Insert newp at this->nextp
    void addHereThisAsNext(AstNode* newp);  // Adds at old place of this, this becomes next
    void replaceWith(AstNode* newp);  // Replace current node in tree with new node
    AstNode* unlinkFrBack(VNRelinker* linkerp
                          = nullptr);  // Unlink this from whoever points to it.
    // Unlink this from whoever points to it, keep entire next list with unlinked node
    AstNode* unlinkFrBackWithNext(VNRelinker* linkerp = nullptr);
    void swapWith(AstNode* bp);
    void relink(VNRelinker* linkerp);  // Generally use linker->relink() instead
    void cloneRelinkNode() { cloneRelink(); }
    // Iterate and insert - assumes tree format
    virtual void addNextStmt(AstNode* newp,
                             AstNode* belowp);  // When calling, "this" is second argument
    virtual void addBeforeStmt(AstNode* newp,
                               AstNode* belowp);  // When calling, "this" is second argument

    // METHODS - Iterate on a tree
    // Clone or return nullptr if nullptr
    static AstNode* cloneTreeNull(AstNode* nodep, bool cloneNextLink) {
        return nodep ? nodep->cloneTree(cloneNextLink) : nullptr;
    }
    AstNode* cloneTree(bool cloneNextLink);  // Not const, as sets clonep() on original nodep
    bool gateTree() { return gateTreeIter(); }  // Is tree isGateOptimizable?
    inline bool sameTree(const AstNode* node2p) const;  // Does tree of this == node2p?
    // Does tree of this == node2p?, not allowing non-isGateOptimizable
    inline bool sameGateTree(const AstNode* node2p) const;
    void deleteTree();  // Always deletes the next link
    void checkTree() const VL_MT_SAFE {
        if (v3Global.opt.debugCheck()) checkTreeIter(backp());
    }
    void checkIter() const;
    void dumpPtrs(std::ostream& os = std::cout) const;
    void dumpTree(std::ostream& os = std::cout, const string& indent = "    ",
                  int maxDepth = 0) const;
    void dumpTree(const string& indent, int maxDepth = 0) const {
        dumpTree(cout, indent, maxDepth);
    }
    static void dumpTreeGdb(const AstNode* nodep);  // For GDB only
    void dumpTreeAndNext(std::ostream& os = std::cout, const string& indent = "    ",
                         int maxDepth = 0) const;
    void dumpTreeFile(const string& filename, bool append = false, bool doDump = true,
                      bool doCheck = true);
    static void dumpTreeFileGdb(const AstNode* nodep, const char* filenamep = nullptr);
    void dumpTreeDot(std::ostream& os = std::cout) const;
    void dumpTreeDotFile(const string& filename, bool append = false, bool doDump = true);

    // METHODS - queries
    // Changes control flow, disable some optimizations
    virtual bool isBrancher() const { return false; }
    // Else a AstTime etc that can't be pushed out
    virtual bool isGateOptimizable() const { return !isTimingControl(); }
    // GateDedupable is a slightly larger superset of GateOptimzable (eg, AstNodeIf)
    virtual bool isGateDedupable() const { return isGateOptimizable(); }
    // Else creates output or exits, etc, not unconsumed
    virtual bool isOutputter() const { return false; }
    // Else a AstTime etc which output can't be predicted from input
    virtual bool isPredictOptimizable() const { return !isTimingControl(); }
    // Else a $display, etc, that must be ordered with other displays
    virtual bool isPure() const { return true; }
    // Else a AstTime etc that can't be substituted out
    virtual bool isSubstOptimizable() const { return true; }
    // An event control, delay, wait, etc.
    virtual bool isTimingControl() const { return false; }
    // isUnlikely handles $stop or similar statement which means an above IF
    // statement is unlikely to be taken
    virtual bool isUnlikely() const { return false; }
    virtual int instrCount() const { return 0; }
    virtual bool same(const AstNode*) const { return true; }
    // Iff has a data type; dtype() must be non null
    virtual bool hasDType() const VL_MT_SAFE { return false; }
    // Iff has a non-null childDTypep(), as generic node function
    virtual AstNodeDType* getChildDTypep() const { return nullptr; }
    // Iff has a non-null child2DTypep(), as generic node function
    virtual AstNodeDType* getChild2DTypep() const { return nullptr; }
    // Another AstNode* may have a pointer into this node, other then normal front/back/etc.
    virtual bool maybePointedTo() const VL_MT_SAFE { return false; }
    // Don't reclaim this node in V3Dead
    virtual bool undead() const { return false; }
    // Check if node is consistent, return nullptr if ok, else reason string
    virtual const char* broken() const { return nullptr; }

    // INVOKERS
    virtual void accept(VNVisitor& v) = 0;

protected:
    // All VNVisitor related functions are called as methods off the visitor
    friend class VNVisitor;
    // Use instead VNVisitor::iterateChildren
    void iterateChildren(VNVisitor& v);
    // Use instead VNVisitor::iterateChildrenBackwards
    void iterateChildrenBackwards(VNVisitor& v);
    // Use instead VNVisitor::iterateChildrenConst
    void iterateChildrenConst(VNVisitor& v);
    // Use instead VNVisitor::iterateAndNextNull
    void iterateAndNext(VNVisitor& v);
    // Use instead VNVisitor::iterateAndNextConstNull
    void iterateAndNextConst(VNVisitor& v);
    // Use instead VNVisitor::iterateSubtreeReturnEdits
    AstNode* iterateSubtreeReturnEdits(VNVisitor& v);

private:
    void iterateListBackwards(VNVisitor& v);

    // For internal use only.
    // Note: specializations for particular node types are provided by 'astgen'
    template <typename T>
    inline static bool privateTypeTest(const AstNode* nodep);

    // For internal use only.
    template <typename TargetType, typename DeclType>
    constexpr static bool uselessCast() {
        using NonRef = typename std::remove_reference<DeclType>::type;
        using NonPtr = typename std::remove_pointer<NonRef>::type;
        using NonCV = typename std::remove_cv<NonPtr>::type;
        return std::is_base_of<TargetType, NonCV>::value;
    }

    // For internal use only.
    template <typename TargetType, typename DeclType>
    constexpr static bool impossibleCast() {
        using NonRef = typename std::remove_reference<DeclType>::type;
        using NonPtr = typename std::remove_pointer<NonRef>::type;
        using NonCV = typename std::remove_cv<NonPtr>::type;
        return !std::is_base_of<NonCV, TargetType>::value;
    }

public:
    // For use via the VN_IS macro only
    template <typename T, typename E>
    static bool privateIs(const AstNode* nodep) VL_MT_SAFE {
        static_assert(!uselessCast<T, E>(), "Unnecessary VN_IS, node known to have target type.");
        static_assert(!impossibleCast<T, E>(), "Unnecessary VN_IS, node cannot be this type.");
        return nodep && privateTypeTest<T>(nodep);
    }

    // For use via the VN_CAST macro only
    template <typename T, typename E>
    static T* privateCast(AstNode* nodep) VL_MT_SAFE {
        static_assert(!uselessCast<T, E>(),
                      "Unnecessary VN_CAST, node known to have target type.");
        static_assert(!impossibleCast<T, E>(), "Unnecessary VN_CAST, node cannot be this type.");
        return nodep && privateTypeTest<T>(nodep) ? reinterpret_cast<T*>(nodep) : nullptr;
    }
    template <typename T, typename E>
    static const T* privateCast(const AstNode* nodep) VL_MT_SAFE {
        static_assert(!uselessCast<T, E>(),
                      "Unnecessary VN_CAST, node known to have target type.");
        static_assert(!impossibleCast<T, E>(), "Unnecessary VN_CAST, node cannot be this type.");
        return nodep && privateTypeTest<T>(nodep) ? reinterpret_cast<const T*>(nodep) : nullptr;
    }

    // For use via the VN_AS macro only
    template <typename T, typename E>
    static T* privateAs(AstNode* nodep) VL_MT_SAFE {
        static_assert(!uselessCast<T, E>(), "Unnecessary VN_AS, node known to have target type.");
        static_assert(!impossibleCast<T, E>(), "Unnecessary VN_AS, node cannot be this type.");
        UASSERT_OBJ(!nodep || privateTypeTest<T>(nodep), nodep,
                    "AstNode is not of expected type, but instead has type '" << nodep->typeName()
                                                                              << "'");
        return reinterpret_cast<T*>(nodep);
    }
    template <typename T, typename E>
    static const T* privateAs(const AstNode* nodep) VL_MT_SAFE {
        static_assert(!uselessCast<T, E>(), "Unnecessary VN_AS, node known to have target type.");
        static_assert(!impossibleCast<T, E>(), "Unnecessary VN_AS, node cannot be this type.");
        UASSERT_OBJ(!nodep || privateTypeTest<T>(nodep), nodep,
                    "AstNode is not of expected type, but instead has type '" << nodep->typeName()
                                                                              << "'");
        return reinterpret_cast<const T*>(nodep);
    }

    // Predicate that returns true if the given 'nodep' might have a descendant of type 'T_Node'.
    // This is conservative and is used to speed up traversals.
    // Note: specializations for particular node types are provided below
    template <typename T_Node>
    static bool mayBeUnder(const AstNode* nodep) {
        static_assert(!std::is_const<T_Node>::value,
                      "Type parameter 'T_Node' should not be const qualified");
        static_assert(std::is_base_of<AstNode, T_Node>::value,
                      "Type parameter 'T_Node' must be a subtype of AstNode");
        return true;
    }

    // Predicate that is true for node subtypes 'T_Node' that do not have any children
    // This is conservative and is used to speed up traversals.
    // Note: specializations for particular node types are provided below
    template <typename T_Node>
    static constexpr bool isLeaf() {
        static_assert(!std::is_const<T_Node>::value,
                      "Type parameter 'T_Node' should not be const qualified");
        static_assert(std::is_base_of<AstNode, T_Node>::value,
                      "Type parameter 'T_Node' must be a subtype of AstNode");
        return false;
    }

private:
    // Using std::conditional for const correctness in the public 'foreach' functions
    template <typename T_Arg>
    using ConstCorrectAstNode =
        typename std::conditional<std::is_const<T_Arg>::value, const AstNode, AstNode>::type;

    template <typename T_Arg, typename Callable>
    inline static void foreachImpl(ConstCorrectAstNode<T_Arg>* nodep, const Callable& f,
                                   bool visitNext);

    template <typename T_Arg, bool Default, typename Callable>
    inline static bool predicateImpl(ConstCorrectAstNode<T_Arg>* nodep, const Callable& p);

    template <typename T_Callable>
    struct Arg0NoPointerNoCV final {
        using Traits = FunctionTraits<T_Callable>;
        using T_Arg0 = typename Traits::template arg<0>::type;
        using T_Arg0NoPtr = typename std::remove_pointer<T_Arg0>::type;
        using type = typename std::remove_cv<T_Arg0NoPtr>::type;
    };

public:
    // Given a callable 'f' that takes a single argument of some AstNode subtype 'T_Node', traverse
    // the tree rooted at this node, and call 'f' in pre-order on each node that is of type
    // 'T_Node'. The node passed to the callable 'f' can be removed or replaced, but other editing
    // of the iterated tree is not safe. Prefer 'foreach' over simple VNVisitor that only needs to
    // handle a single (or a few) node types, as it's easier to write, but more importantly, the
    // dispatch to the callable in 'foreach' should be completely predictable by branch target
    // caches in modern CPUs, while it is basically unpredictable for VNVisitor.
    template <typename Callable>
    void foreach(Callable&& f) {
        using T_Node = typename Arg0NoPointerNoCV<Callable>::type;
        static_assert(vlstd::is_invocable<Callable, T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Callable 'f' must have a signature compatible with 'void(T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        foreachImpl<T_Node>(this, f, /* visitNext: */ false);
    }

    // Same as above, but for 'const' nodes
    template <typename Callable>
    void foreach(Callable&& f) const {
        using T_Node = typename Arg0NoPointerNoCV<Callable>::type;
        static_assert(vlstd::is_invocable<Callable, const T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Callable 'f' must have a signature compatible with 'void(const T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        foreachImpl<const T_Node>(this, f, /* visitNext: */ false);
    }

    // Same as 'foreach' but also traverses 'this->nextp()' transitively
    template <typename Callable>
    void foreachAndNext(Callable&& f) {
        using T_Node = typename Arg0NoPointerNoCV<Callable>::type;
        static_assert(vlstd::is_invocable<Callable, T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Callable 'f' must have a signature compatible with 'void(T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        foreachImpl<T_Node>(this, f, /* visitNext: */ true);
    }

    // Same as above, but for 'const' nodes
    template <typename Callable>
    void foreachAndNext(Callable&& f) const {
        using T_Node = typename Arg0NoPointerNoCV<Callable>::type;
        static_assert(vlstd::is_invocable<Callable, const T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Callable 'f' must have a signature compatible with 'void(const T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        foreachImpl<const T_Node>(this, f, /* visitNext: */ true);
    }

    // Given a predicate 'p' that takes a single argument of some AstNode subtype 'T_Node', return
    // true if and only if there exists a node of type 'T_Node' in the tree rooted at this node,
    // that satisfies the predicate 'p'. Returns false if no node of type 'T_Node' is present.
    // Traversal is performed in some arbitrary order and is terminated as soon as the result can
    // be determined.
    template <typename Callable>
    bool exists(Callable&& p) {
        using T_Node = typename Arg0NoPointerNoCV<Callable>::type;
        static_assert(vlstd::is_invocable_r<bool, Callable, T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<T_Node, /* Default: */ false>(this, p);
    }

    // Same as above, but for 'const' nodes
    template <typename Callable>
    bool exists(Callable&& p) const {
        using T_Node = typename Arg0NoPointerNoCV<Callable>::type;
        static_assert(vlstd::is_invocable_r<bool, Callable, const T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(const T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<const T_Node, /* Default: */ false>(this, p);
    }

    // Given a predicate 'p' that takes a single argument of some AstNode subtype 'T_Node', return
    // true if and only if all nodes of type 'T_Node' in the tree rooted at this node satisfy the
    // predicate 'p'. Returns true if no node of type 'T_Node' is present. Traversal is performed
    // in some arbitrary order and is terminated as soon as the result can be determined.
    template <typename Callable>
    bool forall(Callable&& p) {
        using T_Node = typename Arg0NoPointerNoCV<Callable>::type;
        static_assert(vlstd::is_invocable_r<bool, Callable, T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<T_Node, /* Default: */ true>(this, p);
    }

    // Same as above, but for 'const' nodes
    template <typename Callable>
    bool forall(Callable&& p) const {
        using T_Node = typename Arg0NoPointerNoCV<Callable>::type;
        static_assert(vlstd::is_invocable_r<bool, Callable, const T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(const T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<const T_Node, /* Default: */ true>(this, p);
    }

    int nodeCount() const {
        // TODO: this should really return size_t, but need to fix use sites
        int count = 0;
        this->foreach([&count](const AstNode*) { ++count; });
        return count;
    }
};

// Forward declarations of specializations defined in V3Ast.cpp
template <>
AstNode* AstNode::addNext<AstNode, AstNode>(AstNode* nodep, AstNode* newp);

// Inline method implementations
AstNode* AstNode::addNext(AstNode* newp) { return addNext(this, newp); }
void AstNode::addPrev(AstNode* newp) {
    replaceWith(newp);
    newp->addNext(this);
}

// Specialisations of privateTypeTest
#include "V3Ast__gen_type_tests.h"  // From ./astgen

// Specializations of AstNode::mayBeUnder
template <>
inline bool AstNode::mayBeUnder<AstCell>(const AstNode* nodep) {
    return !VN_IS(nodep, NodeStmt) && !VN_IS(nodep, NodeMath);
}
template <>
inline bool AstNode::mayBeUnder<AstNodeAssign>(const AstNode* nodep) {
    return !VN_IS(nodep, NodeMath);
}
template <>
inline bool AstNode::mayBeUnder<AstVarScope>(const AstNode* nodep) {
    if (VN_IS(nodep, VarScope)) return false;  // Should not nest
    if (VN_IS(nodep, Var)) return false;
    if (VN_IS(nodep, Active)) return false;
    if (VN_IS(nodep, NodeStmt)) return false;
    if (VN_IS(nodep, NodeMath)) return false;
    return true;
}
template <>
inline bool AstNode::mayBeUnder<AstExecGraph>(const AstNode* nodep) {
    if (VN_IS(nodep, ExecGraph)) return false;  // Should not nest
    if (VN_IS(nodep, NodeStmt)) return false;  // Should be directly under CFunc
    return true;
}
template <>
inline bool AstNode::mayBeUnder<AstActive>(const AstNode* nodep) {
    return !VN_IS(nodep, Active);  // AstActives do not nest
}
template <>
inline bool AstNode::mayBeUnder<AstScope>(const AstNode* nodep) {
    return !VN_IS(nodep, Scope);  // AstScopes do not nest
}
template <>
inline bool AstNode::mayBeUnder<AstSenTree>(const AstNode* nodep) {
    return !VN_IS(nodep, SenTree);  // AstSenTree do not nest
}

// Specializations of AstNode::isLeaf
template <>
constexpr bool AstNode::isLeaf<AstNodeVarRef>() {
    return true;
}
template <>
constexpr bool AstNode::isLeaf<AstVarRef>() {
    return true;
}
template <>
constexpr bool AstNode::isLeaf<AstVarXRef>() {
    return true;
}

// foreach implementation
template <typename T_Arg, typename Callable>
void AstNode::foreachImpl(ConstCorrectAstNode<T_Arg>* nodep, const Callable& f, bool visitNext) {
    // Pre-order traversal implemented directly (without recursion) for speed reasons. The very
    // first iteration (the one that operates on the input nodep) is special, as we might or
    // might not need to enqueue nodep->nextp() depending on VisitNext, while in all other
    // iterations, we do want to enqueue nodep->nextp(). Duplicating code (via
    // 'foreachImplVisit') for the initial iteration here to avoid an extra branch in the loop

    using T_Arg_NonConst = typename std::remove_const<T_Arg>::type;
    using Node = ConstCorrectAstNode<T_Arg>;

    // Traversal stack
    std::vector<Node*> stack;  // Kept as a vector for easy resizing
    Node** basep = nullptr;  // Pointer to base of stack
    Node** topp = nullptr;  // Pointer to top of stack
    Node** limp = nullptr;  // Pointer to stack limit (when need growing)

    // We prefetch this far into the stack
    constexpr int prefetchDistance = 2;

    // Grow stack to given size
    const auto grow = [&](size_t size) {
        const ptrdiff_t occupancy = topp - basep;
        stack.resize(size);
        basep = stack.data() + prefetchDistance;
        topp = basep + occupancy;
        limp = basep + size - 5;  // We push max 5 items per iteration
    };

    // Initial stack size
    grow(32);

    // We want some non-null pointers at the beginning. These will be prefetched, but not
    // visited, so the root node will suffice. This eliminates needing branches in the loop.
    for (int i = -prefetchDistance; i; ++i) basep[i] = nodep;

    // Visit given node, enqueue children for traversal
    const auto visit = [&](Node* currp) {
        // Type test this node
        if (AstNode::privateTypeTest<T_Arg_NonConst>(currp)) {
            // Call the client function
            f(static_cast<T_Arg*>(currp));
            // Short circuit if iterating leaf nodes
            if VL_CONSTEXPR_CXX17 (isLeaf<T_Arg_NonConst>()) return;
        }

        // Enqueue children for traversal, unless futile
        if (mayBeUnder<T_Arg_NonConst>(currp)) {
            if (AstNode* const op4p = currp->op4p()) *topp++ = op4p;
            if (AstNode* const op3p = currp->op3p()) *topp++ = op3p;
            if (AstNode* const op2p = currp->op2p()) *topp++ = op2p;
            if (AstNode* const op1p = currp->op1p()) *topp++ = op1p;
        }
    };

    // Enqueue the next of the root node, if required
    if (visitNext && nodep->nextp()) *topp++ = nodep->nextp();

    // Visit the root node
    visit(nodep);

    // Visit the rest of the tree
    while (VL_LIKELY(topp > basep)) {
        // Pop next node in the traversal
        Node* const headp = *--topp;

        // Prefetch in case we are ascending the tree
        ASTNODE_PREFETCH_NON_NULL(topp[-prefetchDistance]);

        // Ensure we have stack space for nextp and the 4 children
        if (VL_UNLIKELY(topp >= limp)) grow(stack.size() * 2);

        // Enqueue the next node
        if (headp->nextp()) *topp++ = headp->nextp();

        // Visit the head node
        visit(headp);
    }
}

// predicate implementation
template <typename T_Arg, bool Default, typename Callable>
bool AstNode::predicateImpl(ConstCorrectAstNode<T_Arg>* nodep, const Callable& p) {
    // Implementation similar to foreach, but abort traversal as soon as result is determined
    using T_Arg_NonConst = typename std::remove_const<T_Arg>::type;
    using Node = ConstCorrectAstNode<T_Arg>;

    // Traversal stack
    std::vector<Node*> stack;  // Kept as a vector for easy resizing
    Node** basep = nullptr;  // Pointer to base of stack
    Node** topp = nullptr;  // Pointer to top of stack
    Node** limp = nullptr;  // Pointer to stack limit (when need growing)

    // We prefetch this far into the stack
    constexpr int prefetchDistance = 2;

    // Grow stack to given size
    const auto grow = [&](size_t size) {
        const ptrdiff_t occupancy = topp - basep;
        stack.resize(size);
        basep = stack.data() + prefetchDistance;
        topp = basep + occupancy;
        limp = basep + size - 5;  // We push max 5 items per iteration
    };

    // Initial stack size
    grow(32);

    // We want some non-null pointers at the beginning. These will be prefetched, but not
    // visited, so the root node will suffice. This eliminates needing branches in the loop.
    for (int i = -prefetchDistance; i; ++i) basep[i] = nodep;

    // Visit given node, enqueue children for traversal, return true if result determined.
    const auto visit = [&](Node* currp) {
        // Type test this node
        if (AstNode::privateTypeTest<T_Arg_NonConst>(currp)) {
            // Call the client function
            if (p(static_cast<T_Arg*>(currp)) != Default) return true;
            // Short circuit if iterating leaf nodes
            if VL_CONSTEXPR_CXX17 (isLeaf<T_Arg_NonConst>()) return false;
        }

        // Enqueue children for traversal, unless futile
        if (mayBeUnder<T_Arg_NonConst>(currp)) {
            if (AstNode* const op4p = currp->op4p()) *topp++ = op4p;
            if (AstNode* const op3p = currp->op3p()) *topp++ = op3p;
            if (AstNode* const op2p = currp->op2p()) *topp++ = op2p;
            if (AstNode* const op1p = currp->op1p()) *topp++ = op1p;
        }

        return false;
    };

    // Visit the root node
    if (visit(nodep)) return !Default;

    // Visit the rest of the tree
    while (VL_LIKELY(topp > basep)) {
        // Pop next node in the traversal
        Node* const headp = *--topp;

        // Prefetch in case we are ascending the tree
        ASTNODE_PREFETCH_NON_NULL(topp[-prefetchDistance]);

        // Ensure we have stack space for nextp and the 4 children
        if (VL_UNLIKELY(topp >= limp)) grow(stack.size() * 2);

        // Enqueue the next node
        if (headp->nextp()) *topp++ = headp->nextp();

        // Visit the head node
        if (visit(headp)) return !Default;
    }

    return Default;
}

inline std::ostream& operator<<(std::ostream& os, const AstNode* rhs) {
    if (!rhs) {
        os << "nullptr";
    } else {
        rhs->dump(os);
    }
    return os;
}
void VNRelinker::relink(AstNode* newp) { newp->AstNode::relink(this); }

//######################################################################

// VNRef is std::reference_wrapper that can only hold AstNode subtypes
template <typename T_Node>
class VNRef final : public std::reference_wrapper<T_Node> {
    static_assert(std::is_base_of<AstNode, T_Node>::value,
                  "Type parameter 'T_Node' must be a subtype of AstNode");

public:
    template <typename U>
    VNRef(U&& x)
        : std::reference_wrapper<T_Node>{x} {}

    VNRef(const std::reference_wrapper<T_Node>& other)
        : std::reference_wrapper<T_Node>{other} {}
};

static_assert(sizeof(VNRef<AstNode>) == sizeof(std::reference_wrapper<AstNode>),
              "VNRef should not contain extra members");

// Specializations of std::hash and std::equal_to for VNRef. This in turn
// enables us to use for example std::unordered_set<VNRef<AstNode>> for
// sets using equality (AstNode::sameTree) rather than identity comparisons,
// without having to copy nodes into the collections.

// Forward declaration to avoid including V3Hasher.h which needs V3Ast.h (this file).
size_t V3HasherUncachedHash(const AstNode&);

// Specialization of std::hash for VNRef
template <typename T_Node>
struct std::hash<VNRef<T_Node>> final {
    size_t operator()(VNRef<T_Node> r) const { return V3HasherUncachedHash(r); }
};

// Specialization of std::equal_to for VNRef
template <typename T_Node>
struct std::equal_to<VNRef<T_Node>> final {
    size_t operator()(VNRef<T_Node> ra, VNRef<T_Node> rb) const {
        return ra.get().sameTree(&(rb.get()));
    }
};

//######################################################################
// Inline VNVisitor METHODS

void VNVisitor::iterate(AstNode* nodep) { nodep->accept(*this); }
void VNVisitor::iterateNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->accept(*this);
}
void VNVisitor::iterateChildren(AstNode* nodep) { nodep->iterateChildren(*this); }
void VNVisitor::iterateChildrenBackwards(AstNode* nodep) {
    nodep->iterateChildrenBackwards(*this);
}
void VNVisitor::iterateChildrenConst(AstNode* nodep) { nodep->iterateChildrenConst(*this); }
void VNVisitor::iterateAndNextNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->iterateAndNext(*this);
}
void VNVisitor::iterateAndNextConstNullBackwards(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->iterateListBackwards(*this);
}
void VNVisitor::iterateAndNextConstNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->iterateAndNextConst(*this);
}
AstNode* VNVisitor::iterateSubtreeReturnEdits(AstNode* nodep) {
    return nodep->iterateSubtreeReturnEdits(*this);
}

// Include macros generated by 'astgen'. These include ASTGEN_MEMBERS_Ast<Node>
// for each AstNode sub-type, and ASTGEN_SUPER_<Node> for concrete final
// AstNode sub-types. The generated members include boilerplate methods related
// to cloning, visitor dispatch, and other functionality. ASTGEN_SUPER_<Node>
// is the necessary constructor invocation for concrete AstNode sub-types
// that passes the generated type-id numbers all the way back to AstNode.
// For precise details please read the generated macros.
#include "V3Ast__gen_macros.h"

// AstNode subclasses
#include "V3AstNodeDType.h"
#include "V3AstNodeMath.h"
#include "V3AstNodeOther.h"

// Inline function definitions need to go last
#include "V3AstInlines.h"

#endif  // Guard
