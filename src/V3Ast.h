// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
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

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Number.h"
#include "V3Global.h"

#include <cmath>
#include <unordered_set>

#include "V3Ast__gen_classes.h"  // From ./astgen
// Things like:
//   class V3AstNode;

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
        if (VL_UNCOVERABLE(test)) return #test; \
    } while (false)
// For broken() function, return error string if a base of this class has a match
#define BROKEN_BASE_RTN(test) \
    do { \
        const char* reasonp = (test); \
        if (VL_UNCOVERABLE(reasonp)) return reasonp; \
    } while (false)

// (V)erilator (N)ode is: True if AstNode is of a a given AstType
#define VN_IS(nodep, nodetypename) (AstNode::privateIs<Ast##nodetypename>(nodep))

// (V)erilator (N)ode cast: Cast to given type if can; effectively
// dynamic_cast<nodetypename>(nodep)
#define VN_CAST(nodep, nodetypename) (AstNode::privateCast<Ast##nodetypename>(nodep))
#define VN_CAST_CONST(nodep, nodetypename) (AstNode::privateConstCast<Ast##nodetypename>(nodep))

// (V)erilator (N)ode deleted: Reference to deleted child (for assertions only)
#define VN_DELETED(nodep) VL_UNLIKELY((vluint64_t)(nodep) == 0x1)

//######################################################################

class AstType final {
public:
#include "V3Ast__gen_types.h"  // From ./astgen
    // Above include has:
    //   enum en {...};
    //   const char* ascii() const {...};
    enum en m_e;
    // cppcheck-suppress uninitVar  // responsibility of each subclass
    inline AstType() {}
    // cppcheck-suppress noExplicitConstructor
    inline AstType(en _e)
        : m_e{_e} {}
    explicit inline AstType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
};
inline bool operator==(const AstType& lhs, const AstType& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const AstType& lhs, AstType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(AstType::en lhs, const AstType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const AstType& rhs) { return os << rhs.ascii(); }

//######################################################################

class VLifetime final {
public:
    enum en : uint8_t { NONE, AUTOMATIC, STATIC };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {"NONE", "VAUTOM", "VSTATIC"};
        return names[m_e];
    }
    inline VLifetime()
        : m_e{NONE} {}
    // cppcheck-suppress noExplicitConstructor
    inline VLifetime(en _e)
        : m_e{_e} {}
    explicit inline VLifetime(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    bool isNone() const { return m_e == NONE; }
    bool isAutomatic() const { return m_e == AUTOMATIC; }
    bool isStatic() const { return m_e == STATIC; }
};
inline bool operator==(const VLifetime& lhs, const VLifetime& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VLifetime& lhs, VLifetime::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VLifetime::en lhs, const VLifetime& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VLifetime& rhs) {
    return os << rhs.ascii();
}

//######################################################################

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
    inline VAccess()
        : m_e{READ} {}
    // cppcheck-suppress noExplicitConstructor
    inline VAccess(en _e)
        : m_e{_e} {}
    explicit inline VAccess(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    VAccess invert() const {
        return (m_e == READWRITE) ? VAccess(m_e) : (m_e == WRITE ? VAccess(READ) : VAccess(WRITE));
    }
    bool isReadOnly() const { return m_e == READ; }  // False with READWRITE
    bool isReadOrRW() const { return m_e == READ || m_e == READWRITE; }
    bool isWriteOrRW() const { return m_e == WRITE || m_e == READWRITE; }
    bool isRW() const { return m_e == READWRITE; }
};
inline bool operator==(const VAccess& lhs, const VAccess& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VAccess& lhs, VAccess::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VAccess::en lhs, const VAccess& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VAccess& rhs) { return os << rhs.ascii(); }

//######################################################################

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
    inline VSigning()
        : m_e{UNSIGNED} {}
    // cppcheck-suppress noExplicitConstructor
    inline VSigning(en _e)
        : m_e{_e} {}
    static inline VSigning fromBool(bool isSigned) {  // Factory method
        return isSigned ? VSigning(SIGNED) : VSigning(UNSIGNED);
    }
    explicit inline VSigning(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    inline bool isSigned() const { return m_e == SIGNED; }
    inline bool isNosign() const { return m_e == NOSIGN; }
    // No isUnsigned() as it's ambiguous if NOSIGN should be included or not.
};
inline bool operator==(const VSigning& lhs, const VSigning& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VSigning& lhs, VSigning::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VSigning::en lhs, const VSigning& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VSigning& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class AstPragmaType final {
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
    inline AstPragmaType()
        : m_e{ILLEGAL} {}
    // cppcheck-suppress noExplicitConstructor
    inline AstPragmaType(en _e)
        : m_e{_e} {}
    explicit inline AstPragmaType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
};
inline bool operator==(const AstPragmaType& lhs, const AstPragmaType& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const AstPragmaType& lhs, AstPragmaType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(AstPragmaType::en lhs, const AstPragmaType& rhs) { return lhs == rhs.m_e; }

//######################################################################

class AstCFuncType final {
public:
    enum en : uint8_t {
        FT_NORMAL,
        TRACE_REGISTER,
        TRACE_INIT,
        TRACE_INIT_SUB,
        TRACE_FULL,
        TRACE_FULL_SUB,
        TRACE_CHANGE,
        TRACE_CHANGE_SUB,
        TRACE_CLEANUP
    };
    enum en m_e;
    inline AstCFuncType()
        : m_e{FT_NORMAL} {}
    // cppcheck-suppress noExplicitConstructor
    inline AstCFuncType(en _e)
        : m_e{_e} {}
    explicit inline AstCFuncType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    // METHODS
    bool isTrace() const { return m_e != FT_NORMAL; }
};
inline bool operator==(const AstCFuncType& lhs, const AstCFuncType& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const AstCFuncType& lhs, AstCFuncType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(AstCFuncType::en lhs, const AstCFuncType& rhs) { return lhs == rhs.m_e; }

//######################################################################

class VEdgeType final {
public:
    // REMEMBER to edit the strings below too
    enum en : uint8_t {
        // These must be in general -> most specific order, as we sort by it
        // in V3Const::visit AstSenTree
        ET_ILLEGAL,
        // Involving a variable
        ET_ANYEDGE,  // Default for sensitivities; rip them out
        ET_BOTHEDGE,  // POSEDGE | NEGEDGE
        ET_POSEDGE,
        ET_NEGEDGE,
        ET_HIGHEDGE,  // Is high now (latches)
        ET_LOWEDGE,  // Is low now (latches)
        // Not involving anything
        ET_COMBO,  // Sensitive to all combo inputs to this block
        ET_INITIAL,  // User initial statements
        ET_SETTLE,  // Like combo but for initial wire resolutions after initial statement
        ET_NEVER  // Never occurs (optimized away)
    };
    enum en m_e;
    bool clockedStmt() const {
        static const bool clocked[]
            = {false, false, true, true, true, true, true, false, false, false};
        return clocked[m_e];
    }
    VEdgeType invert() const {
        switch (m_e) {
        case ET_ANYEDGE: return ET_ANYEDGE;
        case ET_BOTHEDGE: return ET_BOTHEDGE;
        case ET_POSEDGE: return ET_NEGEDGE;
        case ET_NEGEDGE: return ET_POSEDGE;
        case ET_HIGHEDGE: return ET_LOWEDGE;
        case ET_LOWEDGE: return ET_HIGHEDGE;
        default: UASSERT_STATIC(0, "Inverting bad edgeType()");
        }
        return VEdgeType::ET_ILLEGAL;
    }
    const char* ascii() const {
        static const char* const names[]
            = {"%E-edge", "ANY",   "BOTH",    "POS",    "NEG",  "HIGH",
               "LOW",     "COMBO", "INITIAL", "SETTLE", "NEVER"};
        return names[m_e];
    }
    const char* verilogKwd() const {
        static const char* const names[]
            = {"%E-edge", "[any]", "edge",      "posedge",  "negedge", "[high]",
               "[low]",   "*",     "[initial]", "[settle]", "[never]"};
        return names[m_e];
    }
    // Return true iff this and the other have mutually exclusive transitions
    bool exclusiveEdge(const VEdgeType& other) const {
        switch (m_e) {
        case VEdgeType::ET_POSEDGE:
            switch (other.m_e) {
            case VEdgeType::ET_NEGEDGE:  // FALLTHRU
            case VEdgeType::ET_LOWEDGE: return true;
            default:;
            }
            break;
        case VEdgeType::ET_NEGEDGE:
            switch (other.m_e) {
            case VEdgeType::ET_POSEDGE:  // FALLTHRU
            case VEdgeType::ET_HIGHEDGE: return true;
            default:;
            }
            break;
        default:;
        }
        return false;
    }
    inline VEdgeType()
        : m_e{ET_ILLEGAL} {}
    // cppcheck-suppress noExplicitConstructor
    inline VEdgeType(en _e)
        : m_e{_e} {}
    explicit inline VEdgeType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
};
inline bool operator==(const VEdgeType& lhs, const VEdgeType& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VEdgeType& lhs, VEdgeType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VEdgeType::en lhs, const VEdgeType& rhs) { return lhs == rhs.m_e; }

//######################################################################

class AstAttrType final {
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
        VAR_CLOCK_ENABLE,               // V3LinkParse moves to AstVar::attrClockEn
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
            "VAR_BASE", "VAR_CLOCK_ENABLE", "VAR_PUBLIC",
            "VAR_PUBLIC_FLAT", "VAR_PUBLIC_FLAT_RD", "VAR_PUBLIC_FLAT_RW",
            "VAR_ISOLATE_ASSIGNMENTS", "VAR_SC_BV", "VAR_SFORMAT", "VAR_CLOCKER",
            "VAR_NO_CLOCKER", "VAR_SPLIT_VAR"
        };
        // clang-format on
        return names[m_e];
    }
    inline AstAttrType()
        : m_e{ILLEGAL} {}
    // cppcheck-suppress noExplicitConstructor
    inline AstAttrType(en _e)
        : m_e{_e} {}
    explicit inline AstAttrType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
};
inline bool operator==(const AstAttrType& lhs, const AstAttrType& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const AstAttrType& lhs, AstAttrType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(AstAttrType::en lhs, const AstAttrType& rhs) { return lhs == rhs.m_e; }

//######################################################################

class AstBasicDTypeKwd final {
public:
    enum en : uint8_t {
        UNKNOWN,
        BIT,
        BYTE,
        CHANDLE,
        EVENTVALUE,  // See comments in t_event_copy as to why this is EVENTVALUE
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
        static const char* const names[]
            = {"%E-unk",       "bit",     "byte",   "chandle",         "event",
               "int",          "integer", "logic",  "longint",         "real",
               "shortint",     "time",    "string", "VerilatedScope*", "char*",
               "VlMTaskState", "IData",   "QData",  "LOGIC_IMPLICIT",  " MAX"};
        return names[m_e];
    }
    const char* dpiType() const {
        static const char* const names[]
            = {"%E-unk",        "svBit",      "char",        "void*",           "char",
               "int",           "%E-integer", "svLogic",     "long long",       "double",
               "short",         "%E-time",    "const char*", "dpiScope",        "const char*",
               "%E-mtaskstate", "IData",      "QData",       "%E-logic-implct", " MAX"};
        return names[m_e];
    }
    static void selfTest() {
        UASSERT(0 == strcmp(AstBasicDTypeKwd(_ENUM_MAX).ascii(), " MAX"),
                "SelfTest: Enum mismatch");
        UASSERT(0 == strcmp(AstBasicDTypeKwd(_ENUM_MAX).dpiType(), " MAX"),
                "SelfTest: Enum mismatch");
    }
    inline AstBasicDTypeKwd()
        : m_e{UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    inline AstBasicDTypeKwd(en _e)
        : m_e{_e} {}
    explicit inline AstBasicDTypeKwd(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    int width() const {
        switch (m_e) {
        case BIT: return 1;  // scalar, can't bit extract unless ranged
        case BYTE: return 8;
        case CHANDLE: return 64;
        case EVENTVALUE: return 1;
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
        return m_e == CHANDLE || m_e == EVENTVALUE || m_e == STRING || m_e == SCOPEPTR
               || m_e == CHARPTR || m_e == UINT32 || m_e == UINT64;
    }
    bool isFourstate() const {
        return m_e == INTEGER || m_e == LOGIC || m_e == LOGIC_IMPLICIT || m_e == TIME;
    }
    bool isZeroInit() const {  // Otherwise initializes to X
        return (m_e == BIT || m_e == BYTE || m_e == CHANDLE || m_e == EVENTVALUE || m_e == INT
                || m_e == LONGINT || m_e == SHORTINT || m_e == STRING || m_e == DOUBLE);
    }
    bool isIntNumeric() const {  // Enum increment supported
        return (m_e == BIT || m_e == BYTE || m_e == INT || m_e == INTEGER || m_e == LOGIC
                || m_e == LONGINT || m_e == SHORTINT || m_e == UINT32 || m_e == UINT64);
    }
    bool isSloppy() const {  // Don't be as anal about width warnings
        return !(m_e == LOGIC || m_e == BIT);
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
    bool isOpaque() const {  // IE not a simple number we can bit optimize
        return (m_e == STRING || m_e == SCOPEPTR || m_e == CHARPTR || m_e == MTASKSTATE
                || m_e == DOUBLE);
    }
    bool isDouble() const { return m_e == DOUBLE; }
    bool isEventValue() const { return m_e == EVENTVALUE; }
    bool isString() const { return m_e == STRING; }
    bool isMTaskState() const { return m_e == MTASKSTATE; }
};
inline bool operator==(const AstBasicDTypeKwd& lhs, const AstBasicDTypeKwd& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const AstBasicDTypeKwd& lhs, AstBasicDTypeKwd::en rhs) {
    return lhs.m_e == rhs;
}
inline bool operator==(AstBasicDTypeKwd::en lhs, const AstBasicDTypeKwd& rhs) {
    return lhs == rhs.m_e;
}

//######################################################################

class VDirection final {
public:
    enum en : uint8_t { NONE, INPUT, OUTPUT, INOUT, REF, CONSTREF };
    enum en m_e;
    inline VDirection()
        : m_e{NONE} {}
    // cppcheck-suppress noExplicitConstructor
    inline VDirection(en _e)
        : m_e{_e} {}
    explicit inline VDirection(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
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
    bool isReadOnly() const { return m_e == INPUT || m_e == CONSTREF; }
    bool isWritable() const { return m_e == OUTPUT || m_e == INOUT || m_e == REF; }
    bool isRefOrConstRef() const { return m_e == REF || m_e == CONSTREF; }
};
inline bool operator==(const VDirection& lhs, const VDirection& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VDirection& lhs, VDirection::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VDirection::en lhs, const VDirection& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VDirection& rhs) {
    return os << rhs.ascii();
}

//######################################################################

/// Boolean or unknown
class VBoolOrUnknown final {
public:
    enum en : uint8_t { BU_FALSE = 0, BU_TRUE = 1, BU_UNKNOWN = 2, _ENUM_END };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    inline VBoolOrUnknown()
        : m_e{BU_UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    inline VBoolOrUnknown(en _e)
        : m_e{_e} {}
    explicit inline VBoolOrUnknown(int _e)
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
inline bool operator==(const VBoolOrUnknown& lhs, const VBoolOrUnknown& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const VBoolOrUnknown& lhs, VBoolOrUnknown::en rhs) {
    return lhs.m_e == rhs;
}
inline bool operator==(VBoolOrUnknown::en lhs, const VBoolOrUnknown& rhs) {
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
    inline VJoinType()
        : m_e{JOIN} {}
    // cppcheck-suppress noExplicitConstructor
    inline VJoinType(en _e)
        : m_e{_e} {}
    explicit inline VJoinType(int _e)
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
inline bool operator==(const VJoinType& lhs, const VJoinType& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VJoinType& lhs, VJoinType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VJoinType::en lhs, const VJoinType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VJoinType& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class AstVarType final {
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
    inline AstVarType()
        : m_e{UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    inline AstVarType(en _e)
        : m_e{_e} {}
    explicit inline AstVarType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
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
inline bool operator==(const AstVarType& lhs, const AstVarType& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const AstVarType& lhs, AstVarType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(AstVarType::en lhs, const AstVarType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const AstVarType& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class VBranchPred final {
public:
    enum en : uint8_t { BP_UNKNOWN = 0, BP_LIKELY, BP_UNLIKELY, _ENUM_END };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    inline VBranchPred()
        : m_e{BP_UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    inline VBranchPred(en _e)
        : m_e{_e} {}
    explicit inline VBranchPred(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
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
inline bool operator==(const VBranchPred& lhs, const VBranchPred& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const VBranchPred& lhs, VBranchPred::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VBranchPred::en lhs, const VBranchPred& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VBranchPred& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class VVarAttrClocker final {
public:
    enum en : uint8_t { CLOCKER_UNKNOWN = 0, CLOCKER_YES, CLOCKER_NO, _ENUM_END };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    inline VVarAttrClocker()
        : m_e{CLOCKER_UNKNOWN} {}
    // cppcheck-suppress noExplicitConstructor
    inline VVarAttrClocker(en _e)
        : m_e{_e} {}
    explicit inline VVarAttrClocker(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
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
inline bool operator==(const VVarAttrClocker& lhs, const VVarAttrClocker& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const VVarAttrClocker& lhs, VVarAttrClocker::en rhs) {
    return lhs.m_e == rhs;
}
inline bool operator==(VVarAttrClocker::en lhs, const VVarAttrClocker& rhs) {
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
    inline VAlwaysKwd()
        : m_e{ALWAYS} {}
    // cppcheck-suppress noExplicitConstructor
    inline VAlwaysKwd(en _e)
        : m_e{_e} {}
    explicit inline VAlwaysKwd(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"always", "always_ff", "always_latch", "always_comb"};
        return names[m_e];
    }
};
inline bool operator==(const VAlwaysKwd& lhs, const VAlwaysKwd& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VAlwaysKwd& lhs, VAlwaysKwd::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VAlwaysKwd::en lhs, const VAlwaysKwd& rhs) { return lhs == rhs.m_e; }

//######################################################################

class VCaseType final {
public:
    enum en : uint8_t { CT_CASE, CT_CASEX, CT_CASEZ, CT_CASEINSIDE };
    enum en m_e;
    inline VCaseType()
        : m_e{CT_CASE} {}
    // cppcheck-suppress noExplicitConstructor
    inline VCaseType(en _e)
        : m_e{_e} {}
    explicit inline VCaseType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
};
inline bool operator==(const VCaseType& lhs, const VCaseType& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VCaseType& lhs, VCaseType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VCaseType::en lhs, const VCaseType& rhs) { return lhs == rhs.m_e; }

//######################################################################

class AstDisplayType final {
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
    AstDisplayType()
        : m_e{DT_DISPLAY} {}
    // cppcheck-suppress noExplicitConstructor
    AstDisplayType(en _e)
        : m_e{_e} {}
    explicit inline AstDisplayType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    bool addNewline() const { return m_e != DT_WRITE; }
    bool needScopeTracking() const { return m_e != DT_DISPLAY && m_e != DT_WRITE; }
    const char* ascii() const {
        static const char* const names[]
            = {"display", "write", "monitor", "strobe", "info", "error", "warning", "fatal"};
        return names[m_e];
    }
};
inline bool operator==(const AstDisplayType& lhs, const AstDisplayType& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const AstDisplayType& lhs, AstDisplayType::en rhs) {
    return lhs.m_e == rhs;
}
inline bool operator==(AstDisplayType::en lhs, const AstDisplayType& rhs) {
    return lhs == rhs.m_e;
}

//######################################################################

class VDumpCtlType final {
public:
    enum en : uint8_t { FILE, VARS, ALL, FLUSH, LIMIT, OFF, ON };
    enum en m_e;
    inline VDumpCtlType()
        : m_e{ON} {}
    // cppcheck-suppress noExplicitConstructor
    inline VDumpCtlType(en _e)
        : m_e{_e} {}
    explicit inline VDumpCtlType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"$dumpfile",  "$dumpvars", "$dumpall", "$dumpflush",
                                            "$dumplimit", "$dumpoff",  "$dumpon"};
        return names[m_e];
    }
};
inline bool operator==(const VDumpCtlType& lhs, const VDumpCtlType& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const VDumpCtlType& lhs, VDumpCtlType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VDumpCtlType::en lhs, const VDumpCtlType& rhs) { return lhs == rhs.m_e; }

//######################################################################

class VParseRefExp final {
public:
    enum en : uint8_t {
        PX_NONE,  // Used in V3LinkParse only
        PX_ROOT,
        PX_TEXT  // Unknown ID component
    };
    enum en m_e;
    inline VParseRefExp()
        : m_e{PX_NONE} {}
    // cppcheck-suppress noExplicitConstructor
    inline VParseRefExp(en _e)
        : m_e{_e} {}
    explicit inline VParseRefExp(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"", "$root", "TEXT", "PREDOT"};
        return names[m_e];
    }
};
inline bool operator==(const VParseRefExp& lhs, const VParseRefExp& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const VParseRefExp& lhs, VParseRefExp::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VParseRefExp::en lhs, const VParseRefExp& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VParseRefExp& rhs) {
    return os << rhs.ascii();
}

//######################################################################
// VNumRange - Structure containing numeric range information
// See also AstRange, which is a symbolic version of this

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
    VNumRange() {}
    VNumRange(int hi, int lo, bool littleEndian) { init(hi, lo, littleEndian); }
    VNumRange(int left, int right)
        : m_left{left}
        , m_right{right}
        , m_ranged{true} {}
    ~VNumRange() = default;
    // MEMBERS
    void init(int hi, int lo, bool littleEndian) {
        if (lo > hi) {
            int t = hi;
            hi = lo;
            lo = t;
        }
        m_left = littleEndian ? lo : hi;
        m_right = littleEndian ? hi : lo;
        m_ranged = true;
    }
    int left() const { return m_left; }
    int right() const { return m_right; }
    int hi() const { return m_left > m_right ? m_left : m_right; }  // How to show a declaration
    int lo() const { return m_left > m_right ? m_right : m_left; }  // How to show a declaration
    int leftToRightInc() const { return littleEndian() ? 1 : -1; }
    int elements() const { return hi() - lo() + 1; }
    bool ranged() const { return m_ranged; }
    bool littleEndian() const { return m_left < m_right; }
    int hiMaxSelect() const {
        return (lo() < 0 ? hi() - lo() : hi());
    }  // Maximum value a [] select may index
    bool representableByWidth() const {  // Could be represented by just width=1, or [width-1:0]
        return (!m_ranged || (m_right == 0 && m_left >= 1));
    }
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
    inline VUseType()
        : m_e{IMP_FWD_CLASS} {}
    // cppcheck-suppress noExplicitConstructor
    inline VUseType(en _e)
        : m_e{_e} {}
    explicit inline VUseType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    bool isInclude() const { return m_e == IMP_INCLUDE || m_e == INT_INCLUDE; }
    bool isFwdClass() const { return m_e == IMP_FWD_CLASS || m_e == INT_FWD_CLASS; }
    operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"IMP_INC", "INT_INC", "IMP_FWD", "INT_FWD"};
        return names[m_e];
    }
};
inline bool operator==(const VUseType& lhs, const VUseType& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VUseType& lhs, VUseType::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VUseType::en lhs, const VUseType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VUseType& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class VBasicTypeKey final {
public:
    int m_width;  // From AstNodeDType: Bit width of operation
    int m_widthMin;  // From AstNodeDType: If unsized, bitwidth of minimum implementation
    VSigning m_numeric;  // From AstNodeDType: Node is signed
    AstBasicDTypeKwd m_keyword;  // From AstBasicDType: What keyword created basic type
    VNumRange m_nrange;  // From AstBasicDType: Numeric msb/lsb (if non-opaque keyword)
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
    VBasicTypeKey(int width, int widthMin, VSigning numeric, AstBasicDTypeKwd kwd,
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
    VNUser() {}
    // non-explicit:
    // cppcheck-suppress noExplicitConstructor
    VNUser(int i) {
        m_u.up = 0;
        m_u.ui = i;
    }
    explicit VNUser(void* p) { m_u.up = p; }
    ~VNUser() = default;
    // Casters
    WidthVP* c() const { return reinterpret_cast<WidthVP*>(m_u.up); }
    VSymEnt* toSymEnt() const { return reinterpret_cast<VSymEnt*>(m_u.up); }
    AstNode* toNodep() const { return reinterpret_cast<AstNode*>(m_u.up); }
    V3GraphVertex* toGraphVertex() const { return reinterpret_cast<V3GraphVertex*>(m_u.up); }
    int toInt() const { return m_u.ui; }
    static VNUser fromInt(int i) { return VNUser(i); }
};

//######################################################################
// AstUserResource - Generic pointer base class for tracking usage of user()
//
//  Where AstNode->user2() is going to be used, for example, you write:
//
//      AstUser2InUse  m_userres;
//
//  This will clear the tree, and prevent another visitor from clobbering
//  user2.  When the member goes out of scope it will be automagically
//  freed up.

class AstUserInUseBase VL_NOT_FINAL {
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
class AstUser1InUse final : AstUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    AstUser1InUse()     { allocate(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~AstUser1InUse()    { free    (1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class AstUser2InUse final : AstUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    AstUser2InUse()     { allocate(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~AstUser2InUse()    { free    (2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class AstUser3InUse final : AstUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    AstUser3InUse()     { allocate(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~AstUser3InUse()    { free    (3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class AstUser4InUse final : AstUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    AstUser4InUse()     { allocate(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~AstUser4InUse()    { free    (4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class AstUser5InUse final : AstUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t     s_userCntGbl;   // Count of which usage of userp() this is
    static bool         s_userBusy;     // Count is in use
public:
    AstUser5InUse()     { allocate(5, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~AstUser5InUse()    { free    (5, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(5, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(5, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
// clang-format on

//######################################################################
// AstNVisitor -- Allows new functions to be called on each node
// type without changing the base classes.  See "Modern C++ Design".

class AstNVisitor VL_NOT_FINAL {
private:
    // MEMBERS
    std::vector<AstNode*> m_deleteps;  // Nodes to delete when doDeletes() called
protected:
    friend class AstNode;

public:
    // METHODS
    /// At the end of the visitor (or doDeletes()), delete this pushed node
    /// along with all children and next(s). This is often better to use
    /// than an immediate deleteTree, as any pointers into this node will
    /// persist for the lifetime of the visitor
    void pushDeletep(AstNode* nodep) {
        UASSERT_STATIC(nodep, "Cannot delete nullptr node");
        m_deleteps.push_back(nodep);
    }
    /// Call deleteTree on all previously pushDeletep()'ed nodes
    void doDeletes();

public:
    virtual ~AstNVisitor() { doDeletes(); }
    /// Call visit()s on nodep
    void iterate(AstNode* nodep);
    /// Call visit()s on nodep
    void iterateNull(AstNode* nodep);
    /// Call visit()s on nodep's children
    void iterateChildren(AstNode* nodep);
    /// Call visit()s on nodep's children in backp() order
    void iterateChildrenBackwards(AstNode* nodep);
    /// Call visit()s on const nodep's children
    void iterateChildrenConst(AstNode* nodep);
    /// Call visit()s on nodep (maybe nullptr) and nodep's nextp() list
    void iterateAndNextNull(AstNode* nodep);
    /// Call visit()s on const nodep (maybe nullptr) and nodep's nextp() list
    void iterateAndNextConstNull(AstNode* nodep);
    /// Return edited nodep; see comments in V3Ast.cpp
    AstNode* iterateSubtreeReturnEdits(AstNode* nodep);

#include "V3Ast__gen_visitor.h"  // From ./astgen
    // Things like:
    //  virtual void visit(AstBreak* nodep) { visit((AstNodeStmt*)(nodep)); }
    //  virtual void visit(AstNodeStmt* nodep) { visit((AstNode*)(nodep)); }
};

//######################################################################
// AstNRelinker -- Holds the state of a unlink so a new node can be
// added at the same point.

class AstNRelinker final {
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
    AstNRelinker() = default;
    void relink(AstNode* newp);
    AstNode* oldp() const { return m_oldp; }
    void dump(std::ostream& str = std::cout) const;
};
inline std::ostream& operator<<(std::ostream& os, const AstNRelinker& rhs) {
    rhs.dump(os);
    return os;
}

//######################################################################
// Callback base class to determine if node matches some formula

class VNodeMatcher VL_NOT_FINAL {
public:
    virtual bool nodeMatch(const AstNode* nodep) const { return true; }
};

//######################################################################
// AstNode -- Base type of all Ast types

// Prefetch a node.
// The if() makes it faster, even though prefetch won't fault on null pointers
#define ASTNODE_PREFETCH(nodep) \
    do { \
        if (nodep) { \
            VL_PREFETCH_RD(&((nodep)->m_nextp)); \
            VL_PREFETCH_RD(&((nodep)->m_type)); \
        } \
    } while (false)

class AstNode VL_NOT_FINAL {
    // v ASTNODE_PREFETCH depends on below ordering of members
    AstNode* m_nextp;  // Next peer in the parent's list
    AstNode* m_backp;  // Node that points to this one (via next/op1/op2/...)
    AstNode* m_op1p;  // Generic pointer 1
    AstNode* m_op2p;  // Generic pointer 2
    AstNode* m_op3p;  // Generic pointer 3
    AstNode* m_op4p;  // Generic pointer 4
    AstNode** m_iterpp;  // Pointer to node iterating on, change it if we replace this node.
    const AstType m_type;  // Node sub-type identifier
    // ^ ASTNODE_PREFETCH depends on above ordering of members

    // padding - 2 extra bytes here after m_type
    int m_cloneCnt;  // Mark of when userp was set

    AstNodeDType* m_dtypep;  // Data type of output or assignment (etc)
    AstNode* m_headtailp;  // When at begin/end of list, the opposite end of the list
    FileLine* m_fileline;  // Where it was declared
    vluint64_t m_editCount;  // When it was last edited
    static vluint64_t s_editCntGbl;  // Global edit counter
    // Global edit counter, last value for printing * near node #s
    static vluint64_t s_editCntLast;

    AstNode* m_clonep;  // Pointer to clone of/ source of this module (for *LAST* cloneTree() ONLY)
    static int s_cloneCntGbl;  // Count of which userp is set

    // Attributes
    bool m_didWidth : 1;  // Did V3Width computation
    bool m_doingWidth : 1;  // Inside V3Width
    bool m_protect : 1;  // Protect name if protection is on
    //          // Space for more bools here

    // This member ordering both allows 64 bit alignment and puts associated data together
    VNUser m_user1u;  // Contains any information the user iteration routine wants
    uint32_t m_user1Cnt;  // Mark of when userp was set
    uint32_t m_user2Cnt;  // Mark of when userp was set
    VNUser m_user2u;  // Contains any information the user iteration routine wants
    VNUser m_user3u;  // Contains any information the user iteration routine wants
    uint32_t m_user3Cnt;  // Mark of when userp was set
    uint32_t m_user4Cnt;  // Mark of when userp was set
    VNUser m_user4u;  // Contains any information the user iteration routine wants
    VNUser m_user5u;  // Contains any information the user iteration routine wants
    uint32_t m_user5Cnt;  // Mark of when userp was set

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
    void checkTreeIter(AstNode* backp);
    void checkTreeIterList(AstNode* backp);
    bool gateTreeIter() const;
    static bool sameTreeIter(const AstNode* node1p, const AstNode* node2p, bool ignNext,
                             bool gateOnly);
    void deleteTreeIter();
    void deleteNode();
    string locationStr() const;

public:
    static void relinkOneLink(AstNode*& pointpr, AstNode* newp);
    // cppcheck-suppress functionConst
    void debugTreeChange(const char* prefix, int lineno, bool next);

protected:
    // CONSTRUCTORS
    AstNode(AstType t, FileLine* fl);
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
    inline AstType type() const { return m_type; }
    const char* typeName() const { return type().ascii(); }  // See also prettyTypeName
    AstNode* nextp() const { return m_nextp; }
    AstNode* backp() const { return m_backp; }
    AstNode* abovep() const;  // Parent node above, only when no nextp() as otherwise slow
    AstNode* op1p() const { return m_op1p; }
    AstNode* op2p() const { return m_op2p; }
    AstNode* op3p() const { return m_op3p; }
    AstNode* op4p() const { return m_op4p; }
    AstNodeDType* dtypep() const { return m_dtypep; }
    AstNode* clonep() const { return ((m_cloneCnt == s_cloneCntGbl) ? m_clonep : nullptr); }
    AstNode* firstAbovep() const {  // Returns nullptr when second or later in list
        return ((backp() && backp()->nextp() != this) ? backp() : nullptr);
    }
    bool brokeExists() const;
    bool brokeExistsAbove() const;
    bool brokeExistsBelow() const;

    // CONSTRUCTORS
    virtual ~AstNode() = default;
#ifdef VL_LEAK_CHECKS
    static void* operator new(size_t size);
    static void operator delete(void* obj, size_t size);
#endif

    // CONSTANT ACCESSORS
    static int instrCountBranch() { return 4; }  ///< Instruction cycles to branch
    static int instrCountDiv() { return 10; }  ///< Instruction cycles to divide
    static int instrCountDpi() { return 1000; }  ///< Instruction cycles to call user function
    static int instrCountLd() { return 2; }  ///< Instruction cycles to load memory
    static int instrCountMul() { return 3; }  ///< Instruction cycles to multiply integers
    static int instrCountPli() { return 20; }  ///< Instruction cycles to call pli routines
    static int instrCountDouble() { return 8; }  ///< Instruction cycles to convert or do floats
    static int instrCountDoubleDiv() { return 40; }  ///< Instruction cycles to divide floats
    static int instrCountDoubleTrig() { return 200; }  ///< Instruction cycles to do trigonomics
    static int instrCountString() { return 100; }  ///< Instruction cycles to do string ops
    /// Instruction cycles to call subroutine
    static int instrCountCall() { return instrCountBranch() + 10; }
    /// Instruction cycles to determine simulation time
    static int instrCountTime() { return instrCountCall() + 5; }

    // ACCESSORS
    virtual string name() const { return ""; }
    virtual string origName() const { return ""; }
    virtual void name(const string& name) {
        this->v3fatalSrc("name() called on object without name() method");
    }
    virtual void tag(const string& text) {}
    virtual string tag() const { return ""; }
    virtual string verilogKwd() const { return ""; }
    string nameProtect() const;  // Name with --protect-id applied
    string origNameProtect() const;  // origName with --protect-id applied
    string shortName() const;  // Name with __PVT__ removed for concatenating scopes
    static string dedotName(const string& namein);  // Name with dots removed
    static string prettyName(const string& namein);  // Name for printing out to the user
    static string prettyNameQ(const string& namein) {  // Quoted pretty name (for errors)
        return string("'") + prettyName(namein) + "'";
    }
    static string
    encodeName(const string& namein);  // Encode user name into internal C representation
    static string encodeNumber(vlsint64_t num);  // Encode number into internal C representation
    static string vcdName(const string& namein);  // Name for printing out to vcd files
    string prettyName() const { return prettyName(name()); }
    string prettyNameQ() const { return prettyNameQ(name()); }
    string prettyTypeName() const;  // "VARREF" for error messages (NOT dtype's pretty name)
    virtual string prettyOperatorName() const { return "operator " + prettyTypeName(); }
    FileLine* fileline() const { return m_fileline; }
    void fileline(FileLine* fl) { m_fileline = fl; }
    bool width1() const;
    int widthInstrs() const;
    void didWidth(bool flag) { m_didWidth = flag; }
    bool didWidth() const { return m_didWidth; }
    bool didWidthAndSet() {
        if (didWidth()) return true;
        didWidth(true);
        return false;
    }
    bool doingWidth() const { return m_doingWidth; }
    void doingWidth(bool flag) { m_doingWidth = flag; }
    bool protect() const { return m_protect; }
    void protect(bool flag) { m_protect = flag; }

    // TODO stomp these width functions out, and call via dtypep() instead
    int width() const;
    int widthMin() const;
    int widthMinV() const {
        return v3Global.widthMinUsage() == VWidthMinUsage::VERILOG_WIDTH ? widthMin() : width();
    }
    int widthWords() const { return VL_WORDS_I(width()); }
    bool isQuad() const { return (width() > VL_IDATASIZE && width() <= VL_QUADSIZE); }
    bool isWide() const { return (width() > VL_QUADSIZE); }
    bool isDouble() const;
    bool isSigned() const;
    bool isString() const;

    // clang-format off
    VNUser      user1u() const {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(AstUser1InUse::s_userBusy, "userp set w/o busy");
        return ((m_user1Cnt==AstUser1InUse::s_userCntGbl) ? m_user1u : VNUser(0));
    }
    AstNode*    user1p() const { return user1u().toNodep(); }
    void        user1u(const VNUser& user) { m_user1u=user; m_user1Cnt=AstUser1InUse::s_userCntGbl; }
    void        user1p(void* userp) { user1u(VNUser(userp)); }
    int         user1() const { return user1u().toInt(); }
    void        user1(int val) { user1u(VNUser(val)); }
    int         user1Inc(int val=1) { int v=user1(); user1(v+val); return v; }
    int         user1SetOnce() { int v=user1(); if (!v) user1(1); return v; }  // Better for cache than user1Inc()
    static void user1ClearTree() { AstUser1InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser      user2u() const {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(AstUser2InUse::s_userBusy, "userp set w/o busy");
        return ((m_user2Cnt==AstUser2InUse::s_userCntGbl) ? m_user2u : VNUser(0));
    }
    AstNode*    user2p() const { return user2u().toNodep(); }
    void        user2u(const VNUser& user) { m_user2u=user; m_user2Cnt=AstUser2InUse::s_userCntGbl; }
    void        user2p(void* userp) { user2u(VNUser(userp)); }
    int         user2() const { return user2u().toInt(); }
    void        user2(int val) { user2u(VNUser(val)); }
    int         user2Inc(int val=1) { int v=user2(); user2(v+val); return v; }
    int         user2SetOnce() { int v=user2(); if (!v) user2(1); return v; }  // Better for cache than user2Inc()
    static void user2ClearTree() { AstUser2InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser      user3u() const {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(AstUser3InUse::s_userBusy, "userp set w/o busy");
        return ((m_user3Cnt==AstUser3InUse::s_userCntGbl) ? m_user3u : VNUser(0));
    }
    AstNode*    user3p() const { return user3u().toNodep(); }
    void        user3u(const VNUser& user) { m_user3u=user; m_user3Cnt=AstUser3InUse::s_userCntGbl; }
    void        user3p(void* userp) { user3u(VNUser(userp)); }
    int         user3() const { return user3u().toInt(); }
    void        user3(int val) { user3u(VNUser(val)); }
    int         user3Inc(int val=1) { int v=user3(); user3(v+val); return v; }
    int         user3SetOnce() { int v=user3(); if (!v) user3(1); return v; }  // Better for cache than user3Inc()
    static void user3ClearTree() { AstUser3InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser      user4u() const {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(AstUser4InUse::s_userBusy, "userp set w/o busy");
        return ((m_user4Cnt==AstUser4InUse::s_userCntGbl) ? m_user4u : VNUser(0));
    }
    AstNode*    user4p() const { return user4u().toNodep(); }
    void        user4u(const VNUser& user) { m_user4u=user; m_user4Cnt=AstUser4InUse::s_userCntGbl; }
    void        user4p(void* userp) { user4u(VNUser(userp)); }
    int         user4() const { return user4u().toInt(); }
    void        user4(int val) { user4u(VNUser(val)); }
    int         user4Inc(int val=1) { int v=user4(); user4(v+val); return v; }
    int         user4SetOnce() { int v=user4(); if (!v) user4(1); return v; }  // Better for cache than user4Inc()
    static void user4ClearTree() { AstUser4InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser      user5u() const {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(AstUser5InUse::s_userBusy, "userp set w/o busy");
        return ((m_user5Cnt==AstUser5InUse::s_userCntGbl) ? m_user5u : VNUser(0));
    }
    AstNode*    user5p() const { return user5u().toNodep(); }
    void        user5u(const VNUser& user) { m_user5u=user; m_user5Cnt=AstUser5InUse::s_userCntGbl; }
    void        user5p(void* userp) { user5u(VNUser(userp)); }
    int         user5() const { return user5u().toInt(); }
    void        user5(int val) { user5u(VNUser(val)); }
    int         user5Inc(int val=1) { int v=user5(); user5(v+val); return v; }
    int         user5SetOnce() { int v=user5(); if (!v) user5(1); return v; }  // Better for cache than user5Inc()
    static void user5ClearTree() { AstUser5InUse::clear(); }  // Clear userp()'s across the entire tree
    // clang-format on

    vluint64_t editCount() const { return m_editCount; }
    void editCountInc() {
        m_editCount = ++s_editCntGbl;  // Preincrement, so can "watch AstNode::s_editCntGbl=##"
    }
    static vluint64_t editCountLast() { return s_editCntLast; }
    static vluint64_t editCountGbl() { return s_editCntGbl; }
    static void editCountSetLast() { s_editCntLast = editCountGbl(); }

    // ACCESSORS for specific types
    // Alas these can't be virtual or they break when passed a nullptr
    bool isZero() const;
    bool isOne() const;
    bool isNeqZero() const;
    bool isAllOnes() const;
    bool isAllOnesV() const;  // Verilog width rules apply

    // METHODS - data type changes especially for initial creation
    void dtypep(AstNodeDType* nodep) {
        if (m_dtypep != nodep) {
            m_dtypep = nodep;
            editCountInc();
        }
    }
    void dtypeFrom(AstNode* fromp) {
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
    void dtypeSetVoid() { dtypep(findVoidDType()); }

    // Data type locators
    AstNodeDType* findBitDType() { return findBasicDType(AstBasicDTypeKwd::LOGIC); }
    AstNodeDType* findDoubleDType() { return findBasicDType(AstBasicDTypeKwd::DOUBLE); }
    AstNodeDType* findStringDType() { return findBasicDType(AstBasicDTypeKwd::STRING); }
    AstNodeDType* findSigned32DType() { return findBasicDType(AstBasicDTypeKwd::INTEGER); }
    AstNodeDType* findUInt32DType() { return findBasicDType(AstBasicDTypeKwd::UINT32); }
    AstNodeDType* findUInt64DType() { return findBasicDType(AstBasicDTypeKwd::UINT64); }
    AstNodeDType* findCHandleDType() { return findBasicDType(AstBasicDTypeKwd::CHANDLE); }
    AstNodeDType* findVoidDType() const;
    AstNodeDType* findQueueIndexDType() const;
    AstNodeDType* findBitDType(int width, int widthMin, VSigning numeric) const;
    AstNodeDType* findLogicDType(int width, int widthMin, VSigning numeric) const;
    AstNodeDType* findLogicRangeDType(const VNumRange& range, int widthMin,
                                      VSigning numeric) const;
    AstNodeDType* findBitRangeDType(const VNumRange& range, int widthMin, VSigning numeric) const;
    AstNodeDType* findBasicDType(AstBasicDTypeKwd kwd) const;
    AstBasicDType* findInsertSameDType(AstBasicDType* nodep);

    // METHODS - dump and error
    void v3errorEnd(std::ostringstream& str) const;
    void v3errorEndFatal(std::ostringstream& str) const VL_ATTR_NORETURN;
    string warnContextPrimary() const { return fileline()->warnContextPrimary(); }
    string warnContextSecondary() const { return fileline()->warnContextSecondary(); }
    string warnMore() const { return fileline()->warnMore(); }
    string warnOther() const { return fileline()->warnOther(); }

    virtual void dump(std::ostream& str = std::cout) const;
    static void dumpGdb(const AstNode* nodep);  // For GDB only
    void dumpGdbHeader() const;

    // METHODS - Tree modifications
    // Returns nodep, adds newp to end of nodep's list
    static AstNode* addNext(AstNode* nodep, AstNode* newp);
    // Returns nodep, adds newp (maybe nullptr) to end of nodep's list
    static AstNode* addNextNull(AstNode* nodep, AstNode* newp);
    inline AstNode* addNext(AstNode* newp) { return addNext(this, newp); }
    inline AstNode* addNextNull(AstNode* newp) { return addNextNull(this, newp); }
    void addNextHere(AstNode* newp);  // Insert newp at this->nextp
    void addPrev(AstNode* newp) {
        replaceWith(newp);
        newp->addNext(this);
    }
    void addHereThisAsNext(AstNode* newp);  // Adds at old place of this, this becomes next
    void replaceWith(AstNode* newp);  // Replace current node in tree with new node
    AstNode* unlinkFrBack(AstNRelinker* linkerp
                          = nullptr);  // Unlink this from whoever points to it.
    // Unlink this from whoever points to it, keep entire next list with unlinked node
    AstNode* unlinkFrBackWithNext(AstNRelinker* linkerp = nullptr);
    void swapWith(AstNode* bp);
    void relink(AstNRelinker* linkerp);  // Generally use linker->relink() instead
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
    bool sameTree(const AstNode* node2p) const;  // Does tree of this == node2p?
    // Does tree of this == node2p?, not allowing non-isGateOptimizable
    bool sameGateTree(const AstNode* node2p) const;
    void deleteTree();  // Always deletes the next link
    void checkTree();  // User Interface version
    void checkIter() const;
    void clearIter() { m_iterpp = nullptr; }
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

    // METHODS - queries
    // Changes control flow, disable some optimizations
    virtual bool isBrancher() const { return false; }
    // Else a AstTime etc that can't be pushed out
    virtual bool isGateOptimizable() const { return true; }
    // GateDedupable is a slightly larger superset of GateOptimzable (eg, AstNodeIf)
    virtual bool isGateDedupable() const { return isGateOptimizable(); }
    // Needs verilated_heavy.h (uses std::string or some others)
    virtual bool isHeavy() const { return false; }
    // Else creates output or exits, etc, not unconsumed
    virtual bool isOutputter() const { return false; }
    // Else a AstTime etc which output can't be predicted from input
    virtual bool isPredictOptimizable() const { return true; }
    // Else a $display, etc, that must be ordered with other displays
    virtual bool isPure() const { return true; }
    // Else a AstTime etc that can't be substituted out
    virtual bool isSubstOptimizable() const { return true; }
    // isUnlikely handles $stop or similar statement which means an above IF
    // statement is unlikely to be taken
    virtual bool isUnlikely() const { return false; }
    virtual int instrCount() const { return 0; }
    virtual bool same(const AstNode*) const { return true; }
    // Iff has a data type; dtype() must be non null
    virtual bool hasDType() const { return false; }
    // Iff has a non-null childDTypep(), as generic node function
    virtual AstNodeDType* getChildDTypep() const { return nullptr; }
    // Iff has a non-null child2DTypep(), as generic node function
    virtual AstNodeDType* getChild2DTypep() const { return nullptr; }
    // Another AstNode* may have a pointer into this node, other then normal front/back/etc.
    virtual bool maybePointedTo() const { return false; }
    virtual const char* broken() const { return nullptr; }

    // INVOKERS
    virtual void accept(AstNVisitor& v) = 0;

protected:
    // All AstNVisitor related functions are called as methods off the visitor
    friend class AstNVisitor;
    // Use instead AstNVisitor::iterateChildren
    void iterateChildren(AstNVisitor& v);
    // Use instead AstNVisitor::iterateChildrenBackwards
    void iterateChildrenBackwards(AstNVisitor& v);
    // Use instead AstNVisitor::iterateChildrenConst
    void iterateChildrenConst(AstNVisitor& v);
    // Use instead AstNVisitor::iterateAndNextNull
    void iterateAndNext(AstNVisitor& v);
    // Use instead AstNVisitor::iterateAndNextConstNull
    void iterateAndNextConst(AstNVisitor& v);
    // Use instead AstNVisitor::iterateSubtreeReturnEdits
    AstNode* iterateSubtreeReturnEdits(AstNVisitor& v);

private:
    void iterateListBackwards(AstNVisitor& v);

    // CONVERSION
public:
    // These for use by VN_IS macro only
    template <class T> static bool privateIs(const AstNode* nodep);

    // These for use by VN_CAST macro only
    template <class T> static T* privateCast(AstNode* nodep);

    // These for use by VN_CAST_CONST macro only
    template <class T> static const T* privateConstCast(const AstNode* nodep);
};

// Specialisations of privateIs/privateCast
#include "V3Ast__gen_impl.h"  // From ./astgen

inline std::ostream& operator<<(std::ostream& os, const AstNode* rhs) {
    if (!rhs) {
        os << "nullptr";
    } else {
        rhs->dump(os);
    }
    return os;
}
inline void AstNRelinker::relink(AstNode* newp) { newp->AstNode::relink(this); }

//######################################################################
//######################################################################
//=== AstNode* : Derived generic node types

#define ASTNODE_BASE_FUNCS(name) \
    virtual ~Ast##name() override = default; \
    static Ast##name* cloneTreeNull(Ast##name* nodep, bool cloneNextLink) { \
        return nodep ? nodep->cloneTree(cloneNextLink) : nullptr; \
    } \
    Ast##name* cloneTree(bool cloneNext) { \
        return static_cast<Ast##name*>(AstNode::cloneTree(cloneNext)); \
    } \
    Ast##name* clonep() const { return static_cast<Ast##name*>(AstNode::clonep()); }

class AstNodeMath VL_NOT_FINAL : public AstNode {
    // Math -- anything that's part of an expression tree
protected:
    AstNodeMath(AstType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTNODE_BASE_FUNCS(NodeMath)
    // METHODS
    virtual void dump(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    virtual string emitVerilog() = 0;  /// Format string for verilog writing; see V3EmitV
    // For documentation on emitC format see EmitCStmts::emitOpName
    virtual string emitC() = 0;
    virtual string emitSimpleOperator() { return ""; }  // "" means not ok to use
    virtual bool emitCheckMaxWords() { return false; }  // Check VL_MULS_MAX_WORDS
    virtual bool cleanOut() const = 0;  // True if output has extra upper bits zero
    // Someday we will generically support data types on every math node
    // Until then isOpaque indicates we shouldn't constant optimize this node type
    bool isOpaque() { return VN_IS(this, CvtPackString); }
};

class AstNodeTermop VL_NOT_FINAL : public AstNodeMath {
    // Terminal operator -- a operator with no "inputs"
protected:
    AstNodeTermop(AstType t, FileLine* fl)
        : AstNodeMath{t, fl} {}

public:
    ASTNODE_BASE_FUNCS(NodeTermop)
    // Know no children, and hot function, so skip iterator for speed
    // See checkTreeIter also that asserts no children
    // cppcheck-suppress functionConst
    void iterateChildren(AstNVisitor& v) {}
    virtual void dump(std::ostream& str) const override;
};

class AstNodeUniop VL_NOT_FINAL : public AstNodeMath {
    // Unary math
protected:
    AstNodeUniop(AstType t, FileLine* fl, AstNode* lhsp)
        : AstNodeMath{t, fl} {
        dtypeFrom(lhsp);
        setOp1p(lhsp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeUniop)
    AstNode* lhsp() const { return op1p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    // METHODS
    virtual void dump(std::ostream& str) const override;
    // Set out to evaluation of a AstConst'ed lhs
    virtual void numberOperate(V3Number& out, const V3Number& lhs) = 0;
    virtual bool cleanLhs() const = 0;
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool doubleFlavor() const { return false; }  // D flavor of nodes with both flavors?
    // Signed flavor of nodes with both flavors?
    virtual bool signedFlavor() const { return false; }
    virtual bool stringFlavor() const { return false; }  // N flavor of nodes with both flavors?
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
};

class AstNodeBiop VL_NOT_FINAL : public AstNodeMath {
    // Binary math
protected:
    AstNodeBiop(AstType t, FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeMath{t, fl} {
        setOp1p(lhs);
        setOp2p(rhs);
    }

public:
    ASTNODE_BASE_FUNCS(NodeBiop)
    // Clone single node, just get same type back.
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) = 0;
    // ACCESSORS
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    // METHODS
    // Set out to evaluation of a AstConst'ed
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) = 0;
    virtual bool cleanLhs() const = 0;  // True if LHS must have extra upper bits zero
    virtual bool cleanRhs() const = 0;  // True if RHS must have extra upper bits zero
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool sizeMattersRhs() const = 0;  // True if output result depends on rhs size
    virtual bool doubleFlavor() const { return false; }  // D flavor of nodes with both flavors?
    // Signed flavor of nodes with both flavors?
    virtual bool signedFlavor() const { return false; }
    virtual bool stringFlavor() const { return false; }  // N flavor of nodes with both flavors?
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
};

class AstNodeTriop VL_NOT_FINAL : public AstNodeMath {
    // Trinary math
protected:
    AstNodeTriop(AstType t, FileLine* fl, AstNode* lhs, AstNode* rhs, AstNode* ths)
        : AstNodeMath{t, fl} {
        setOp1p(lhs);
        setOp2p(rhs);
        setOp3p(ths);
    }

public:
    ASTNODE_BASE_FUNCS(NodeTriop)
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    AstNode* thsp() const { return op3p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    void thsp(AstNode* nodep) { return setOp3p(nodep); }
    // METHODS
    virtual void dump(std::ostream& str) const override;
    // Set out to evaluation of a AstConst'ed
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths)
        = 0;
    virtual bool cleanLhs() const = 0;  // True if LHS must have extra upper bits zero
    virtual bool cleanRhs() const = 0;  // True if RHS must have extra upper bits zero
    virtual bool cleanThs() const = 0;  // True if THS must have extra upper bits zero
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool sizeMattersRhs() const = 0;  // True if output result depends on rhs size
    virtual bool sizeMattersThs() const = 0;  // True if output result depends on ths size
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
};

class AstNodeQuadop VL_NOT_FINAL : public AstNodeMath {
    // Quaternary math
protected:
    AstNodeQuadop(AstType t, FileLine* fl, AstNode* lhs, AstNode* rhs, AstNode* ths, AstNode* fhs)
        : AstNodeMath{t, fl} {
        setOp1p(lhs);
        setOp2p(rhs);
        setOp3p(ths);
        setOp4p(fhs);
    }

public:
    ASTNODE_BASE_FUNCS(NodeQuadop)
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    AstNode* thsp() const { return op3p(); }
    AstNode* fhsp() const { return op4p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    void thsp(AstNode* nodep) { return setOp3p(nodep); }
    void fhsp(AstNode* nodep) { return setOp4p(nodep); }
    // METHODS
    // Set out to evaluation of a AstConst'ed
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths, const V3Number& fhs)
        = 0;
    virtual bool cleanLhs() const = 0;  // True if LHS must have extra upper bits zero
    virtual bool cleanRhs() const = 0;  // True if RHS must have extra upper bits zero
    virtual bool cleanThs() const = 0;  // True if THS must have extra upper bits zero
    virtual bool cleanFhs() const = 0;  // True if THS must have extra upper bits zero
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool sizeMattersRhs() const = 0;  // True if output result depends on rhs size
    virtual bool sizeMattersThs() const = 0;  // True if output result depends on ths size
    virtual bool sizeMattersFhs() const = 0;  // True if output result depends on ths size
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
};

class AstNodeBiCom VL_NOT_FINAL : public AstNodeBiop {
    // Binary math with commutative properties
protected:
    AstNodeBiCom(AstType t, FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeBiop{t, fl, lhs, rhs} {}

public:
    ASTNODE_BASE_FUNCS(NodeBiCom)
};

class AstNodeBiComAsv VL_NOT_FINAL : public AstNodeBiCom {
    // Binary math with commutative & associative properties
protected:
    AstNodeBiComAsv(AstType t, FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeBiCom{t, fl, lhs, rhs} {}

public:
    ASTNODE_BASE_FUNCS(NodeBiComAsv)
};

class AstNodeCond VL_NOT_FINAL : public AstNodeTriop {
protected:
    AstNodeCond(AstType t, FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
        : AstNodeTriop{t, fl, condp, expr1p, expr2p} {
        if (expr1p) {
            dtypeFrom(expr1p);
        } else if (expr2p) {
            dtypeFrom(expr2p);
        }
    }

public:
    ASTNODE_BASE_FUNCS(NodeCond)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override;
    AstNode* condp() const { return op1p(); }  // op1 = Condition
    AstNode* expr1p() const { return op2p(); }  // op2 = If true...
    AstNode* expr2p() const { return op3p(); }  // op3 = If false...
    virtual string emitVerilog() override { return "%k(%l %f? %r %k: %t)"; }
    virtual string emitC() override {
        return "VL_COND_%nq%lq%rq%tq(%nw,%lw,%rw,%tw, %P, %li, %ri, %ti)";
    }
    virtual bool cleanOut() const override { return false; }  // clean if e1 & e2 clean
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }  // Propagates up
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual int instrCount() const override { return instrCountBranch(); }
    virtual AstNode* cloneType(AstNode* condp, AstNode* expr1p, AstNode* expr2p) = 0;
};

class AstNodeBlock VL_NOT_FINAL : public AstNode {
    // A Begin/fork block
    // Parents: statement
    // Children: statements
private:
    string m_name;  // Name of block
    bool m_unnamed;  // Originally unnamed (name change does not affect this)
protected:
    AstNodeBlock(AstType t, FileLine* fl, const string& name, AstNode* stmtsp)
        : AstNode{t, fl}
        , m_name{name} {
        addNOp1p(stmtsp);
        m_unnamed = (name == "");
    }

public:
    ASTNODE_BASE_FUNCS(NodeBlock)
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }  // * = Block name
    virtual void name(const string& name) override { m_name = name; }
    // op1 = Statements
    AstNode* stmtsp() const { return op1p(); }  // op1 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp1p(nodep); }
    bool unnamed() const { return m_unnamed; }
};

class AstNodePreSel VL_NOT_FINAL : public AstNode {
    // Something that becomes an AstSel
protected:
    AstNodePreSel(AstType t, FileLine* fl, AstNode* fromp, AstNode* rhs, AstNode* ths)
        : AstNode{t, fl} {
        setOp1p(fromp);
        setOp2p(rhs);
        setNOp3p(ths);
    }

public:
    ASTNODE_BASE_FUNCS(NodePreSel)
    AstNode* fromp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    AstNode* thsp() const { return op3p(); }
    AstAttrOf* attrp() const { return VN_CAST(op4p(), AttrOf); }
    void fromp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    void thsp(AstNode* nodep) { return setOp3p(nodep); }
    void attrp(AstAttrOf* nodep) { return setOp4p((AstNode*)nodep); }
    // METHODS
    virtual bool same(const AstNode*) const override { return true; }
};

class AstNodeProcedure VL_NOT_FINAL : public AstNode {
    // IEEE procedure: initial, final, always
protected:
    AstNodeProcedure(AstType t, FileLine* fl, AstNode* bodysp)
        : AstNode{t, fl} {
        addNOp2p(bodysp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeProcedure)
    // METHODS
    virtual void dump(std::ostream& str) const override;
    AstNode* bodysp() const { return op2p(); }  // op2 = Statements to evaluate
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};

class AstNodeStmt VL_NOT_FINAL : public AstNode {
    // Statement -- anything that's directly under a function
    bool m_statement;  // Really a statement (e.g. not a function with return)
protected:
    AstNodeStmt(AstType t, FileLine* fl, bool statement = true)
        : AstNode{t, fl}
        , m_statement{statement} {}

public:
    ASTNODE_BASE_FUNCS(NodeStmt)
    // METHODS
    bool isStatement() const { return m_statement; }  // Really a statement
    void statement(bool flag) { m_statement = flag; }
    virtual void addNextStmt(AstNode* newp,
                             AstNode* belowp) override;  // Stop statement searchback here
    virtual void addBeforeStmt(AstNode* newp,
                               AstNode* belowp) override;  // Stop statement searchback here
    virtual void dump(std::ostream& str = std::cout) const override;
};

class AstNodeAssign VL_NOT_FINAL : public AstNodeStmt {
protected:
    AstNodeAssign(AstType t, FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : AstNodeStmt{t, fl} {
        setOp1p(rhsp);
        setOp2p(lhsp);
        dtypeFrom(lhsp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeAssign)
    // Clone single node, just get same type back.
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) = 0;
    // So iteration hits the RHS which is "earlier" in execution order, it's op1, not op2
    AstNode* rhsp() const { return op1p(); }  // op1 = Assign from
    AstNode* lhsp() const { return op2p(); }  // op2 = Assign to
    void rhsp(AstNode* np) { setOp1p(np); }
    void lhsp(AstNode* np) { setOp2p(np); }
    virtual bool hasDType() const override { return true; }
    virtual bool cleanRhs() const { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
    virtual string verilogKwd() const override { return "="; }
    virtual bool brokeLhsMustBeLvalue() const = 0;
};

class AstNodeFor VL_NOT_FINAL : public AstNodeStmt {
protected:
    AstNodeFor(AstType t, FileLine* fl, AstNode* initsp, AstNode* condp, AstNode* incsp,
               AstNode* bodysp)
        : AstNodeStmt{t, fl} {
        addNOp1p(initsp);
        setOp2p(condp);
        addNOp3p(incsp);
        addNOp4p(bodysp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeFor)
    AstNode* initsp() const { return op1p(); }  // op1 = initial statements
    AstNode* condp() const { return op2p(); }  // op2 = condition to continue
    AstNode* incsp() const { return op3p(); }  // op3 = increment statements
    AstNode* bodysp() const { return op4p(); }  // op4 = body of loop
    virtual bool isGateOptimizable() const override { return false; }
    virtual int instrCount() const override { return instrCountBranch(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstNodeIf VL_NOT_FINAL : public AstNodeStmt {
private:
    VBranchPred m_branchPred;  // Branch prediction as taken/untaken?
    bool m_isBoundsCheck;  // True if this if node was inserted for array bounds checking
protected:
    AstNodeIf(AstType t, FileLine* fl, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
        : AstNodeStmt{t, fl} {
        setOp1p(condp);
        addNOp2p(ifsp);
        addNOp3p(elsesp);
        isBoundsCheck(false);
    }

public:
    ASTNODE_BASE_FUNCS(NodeIf)
    AstNode* condp() const { return op1p(); }  // op1 = condition
    AstNode* ifsp() const { return op2p(); }  // op2 = list of true statements
    AstNode* elsesp() const { return op3p(); }  // op3 = list of false statements
    void condp(AstNode* newp) { setOp1p(newp); }
    void addIfsp(AstNode* newp) { addOp2p(newp); }
    void addElsesp(AstNode* newp) { addOp3p(newp); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isGateDedupable() const override { return true; }
    virtual int instrCount() const override { return instrCountBranch(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    void branchPred(VBranchPred flag) { m_branchPred = flag; }
    VBranchPred branchPred() const { return m_branchPred; }
    void isBoundsCheck(bool flag) { m_isBoundsCheck = flag; }
    bool isBoundsCheck() const { return m_isBoundsCheck; }
};

class AstNodeCase VL_NOT_FINAL : public AstNodeStmt {
protected:
    AstNodeCase(AstType t, FileLine* fl, AstNode* exprp, AstNode* casesp)
        : AstNodeStmt{t, fl} {
        setOp1p(exprp);
        addNOp2p(casesp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeCase)
    virtual int instrCount() const override { return instrCountBranch(); }
    AstNode* exprp() const { return op1p(); }  // op1 = case condition <expression>
    AstCaseItem* itemsp() const {
        return VN_CAST(op2p(), CaseItem);
    }  // op2 = list of case expressions
    AstNode* notParallelp() const { return op3p(); }  // op3 = assertion code for non-full case's
    void addItemsp(AstNode* nodep) { addOp2p(nodep); }
    void addNotParallelp(AstNode* nodep) { setOp3p(nodep); }
};

class AstNodeVarRef VL_NOT_FINAL : public AstNodeMath {
    // An AstVarRef or AstVarXRef
private:
    VAccess m_access;  // Left hand side assignment
    AstVar* m_varp;  // [AfterLink] Pointer to variable itself
    AstVarScope* m_varScopep = nullptr;  // Varscope for hierarchy
    AstNodeModule* m_classOrPackagep = nullptr;  // Package hierarchy
    string m_name;  // Name of variable
    string m_selfPointer;  // Output code object pointer (e.g.: 'this')
    string m_classPrefix;  // Output class prefix (i.e.: the part before ::)
    bool m_hierThis = false;  // m_selfPointer points to "this" function

protected:
    AstNodeVarRef(AstType t, FileLine* fl, const string& name, const VAccess& access)
        : AstNodeMath{t, fl}
        , m_access{access}
        , m_name{name} {
        this->varp(nullptr);
    }
    AstNodeVarRef(AstType t, FileLine* fl, const string& name, AstVar* varp, const VAccess& access)
        : AstNodeMath{t, fl}
        , m_access{access}
        , m_name{name} {
        // May have varp==nullptr
        this->varp(varp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeVarRef)
    virtual void dump(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    virtual const char* broken() const override;
    virtual int instrCount() const override { return widthInstrs(); }
    virtual void cloneRelink() override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual void name(const string& name) override { m_name = name; }
    VAccess access() const { return m_access; }
    void access(const VAccess& flag) { m_access = flag; }  // Avoid using this; Set in constructor
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    void varp(AstVar* varp);
    AstVarScope* varScopep() const { return m_varScopep; }
    void varScopep(AstVarScope* varscp) { m_varScopep = varscp; }
    bool hierThis() const { return m_hierThis; }
    void hierThis(bool flag) { m_hierThis = flag; }
    string selfPointer() const { return m_selfPointer; }
    void selfPointer(const string& value) { m_selfPointer = value; }
    string selfPointerProtect(bool useSelfForThis) const;
    string classPrefix() const { return m_classPrefix; }
    void classPrefix(const string& value) { m_classPrefix = value; }
    string classPrefixProtect() const;
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    // Know no children, and hot function, so skip iterator for speed
    // See checkTreeIter also that asserts no children
    // cppcheck-suppress functionConst
    void iterateChildren(AstNVisitor& v) {}
};

class AstNodeText VL_NOT_FINAL : public AstNode {
private:
    string m_text;

protected:
    // Node that simply puts text into the output stream
    AstNodeText(AstType t, FileLine* fl, const string& textp)
        : AstNode{t, fl} {
        m_text = textp;  // Copy it
    }

public:
    ASTNODE_BASE_FUNCS(NodeText)
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual bool same(const AstNode* samep) const override {
        const AstNodeText* asamep = static_cast<const AstNodeText*>(samep);
        return text() == asamep->text();
    }
    const string& text() const { return m_text; }
};

class AstNodeDType VL_NOT_FINAL : public AstNode {
    // Ideally width() would migrate to BasicDType as that's where it makes sense,
    // but it's currently so prevalent in the code we leave it here.
    // Note the below members are included in AstTypeTable::Key lookups
private:
    int m_width;  // (also in AstTypeTable::Key) Bit width of operation
    int m_widthMin;  // (also in AstTypeTable::Key) If unsized, bitwidth of minimum implementation
    VSigning m_numeric;  // (also in AstTypeTable::Key) Node is signed
    // Other members
    bool m_generic;  // Simple globally referenced type, don't garbage collect
    // Unique number assigned to each dtype during creation for IEEE matching
    static int s_uniqueNum;

protected:
    // CONSTRUCTORS
    AstNodeDType(AstType t, FileLine* fl)
        : AstNode{t, fl} {
        m_width = 0;
        m_widthMin = 0;
        m_generic = false;
    }

public:
    ASTNODE_BASE_FUNCS(NodeDType)
    // ACCESSORS
    virtual void dump(std::ostream& str) const override;
    virtual void dumpSmall(std::ostream& str) const;
    virtual bool hasDType() const override { return true; }
    /// Require VlUnpacked, instead of [] for POD elements.
    /// A non-POD object is always compound, but some POD elements
    /// are compound when methods calls operate on object, or when
    /// under another compound-requiring object e.g. class
    virtual bool isCompound() const = 0;
    // (Slow) recurse down to find basic data type
    virtual AstBasicDType* basicp() const = 0;
    // recurses over typedefs/const/enum to next non-typeref type
    virtual AstNodeDType* skipRefp() const = 0;
    // recurses over typedefs to next non-typeref-or-const type
    virtual AstNodeDType* skipRefToConstp() const = 0;
    // recurses over typedefs/const to next non-typeref-or-enum/struct type
    virtual AstNodeDType* skipRefToEnump() const = 0;
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthAlignBytes() const = 0;
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    virtual int widthTotalBytes() const = 0;
    virtual bool maybePointedTo() const override { return true; }
    // Iff has a non-null refDTypep(), as generic node function
    virtual AstNodeDType* virtRefDTypep() const { return nullptr; }
    // Iff has refDTypep(), set as generic node function
    virtual void virtRefDTypep(AstNodeDType* nodep) {}
    // Iff has a non-null second dtypep, as generic node function
    virtual AstNodeDType* virtRefDType2p() const { return nullptr; }
    // Iff has second dtype, set as generic node function
    virtual void virtRefDType2p(AstNodeDType* nodep) {}
    // Assignable equivalence.  Call skipRefp() on this and samep before calling
    virtual bool similarDType(AstNodeDType* samep) const = 0;
    // Iff has a non-null subDTypep(), as generic node function
    virtual AstNodeDType* subDTypep() const { return nullptr; }
    virtual bool isFourstate() const;
    // Ideally an IEEE $typename
    virtual string prettyDTypeName() const { return prettyTypeName(); }
    string prettyDTypeNameQ() const { return "'" + prettyDTypeName() + "'"; }
    //
    // Changing the width may confuse the data type resolution, so must clear
    // TypeTable cache after use.
    void widthForce(int width, int widthMin) {
        m_width = width;
        m_widthMin = widthMin;
    }
    // For backward compatibility inherit width and signing from the subDType/base type
    void widthFromSub(AstNodeDType* nodep) {
        m_width = nodep->m_width;
        m_widthMin = nodep->m_widthMin;
        m_numeric = nodep->m_numeric;
    }
    //
    int width() const { return m_width; }
    void numeric(VSigning flag) { m_numeric = flag; }
    bool isSigned() const { return m_numeric.isSigned(); }
    bool isNosign() const { return m_numeric.isNosign(); }
    VSigning numeric() const { return m_numeric; }
    int widthWords() const { return VL_WORDS_I(width()); }
    int widthMin() const {  // If sized, the size, if unsized the min digits to represent it
        return m_widthMin ? m_widthMin : m_width;
    }
    int widthPow2() const;
    void widthMinFromWidth() { m_widthMin = m_width; }
    bool widthSized() const { return !m_widthMin || m_widthMin == m_width; }
    bool generic() const { return m_generic; }
    void generic(bool flag) { m_generic = flag; }
    std::pair<uint32_t, uint32_t> dimensions(bool includeBasic);
    uint32_t arrayUnpackedElements();  // 1, or total multiplication of all dimensions
    static int uniqueNumInc() { return ++s_uniqueNum; }
    const char* charIQWN() const {
        return (isString() ? "N" : isWide() ? "W" : isQuad() ? "Q" : "I");
    }
    string cType(const string& name, bool forFunc, bool isRef) const;

private:
    class CTypeRecursed;
    CTypeRecursed cTypeRecurse(bool compound) const;
};

class AstNodeUOrStructDType VL_NOT_FINAL : public AstNodeDType {
    // A struct or union; common handling
private:
    // TYPES
    using MemberNameMap = std::map<const std::string, AstMemberDType*>;
    // MEMBERS
    string m_name;  // Name from upper typedef, if any
    bool m_packed;
    bool m_isFourstate;
    MemberNameMap m_members;
    const int m_uniqueNum;

protected:
    AstNodeUOrStructDType(AstType t, FileLine* fl, VSigning numericUnpack)
        : AstNodeDType{t, fl}
        , m_uniqueNum{uniqueNumInc()} {
        // VSigning::NOSIGN overloaded to indicate not packed
        m_packed = (numericUnpack != VSigning::NOSIGN);
        m_isFourstate = false;  // V3Width computes
        numeric(VSigning::fromBool(numericUnpack.isSigned()));
    }

public:
    ASTNODE_BASE_FUNCS(NodeUOrStructDType)
    int uniqueNum() const { return m_uniqueNum; }
    virtual const char* broken() const override;
    virtual void dump(std::ostream& str) const override;
    virtual bool isCompound() const override { return false; }  // Because don't support unpacked
    // For basicp() we reuse the size to indicate a "fake" basic type of same size
    virtual AstBasicDType* basicp() const override {
        return (isFourstate()
                    ? VN_CAST(findLogicRangeDType(VNumRange{width() - 1, 0}, width(), numeric()),
                              BasicDType)
                    : VN_CAST(findBitRangeDType(VNumRange{width() - 1, 0}, width(), numeric()),
                              BasicDType));
    }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthAlignBytes() const override;
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    virtual int widthTotalBytes() const override;
    // op1 = members
    virtual bool similarDType(AstNodeDType* samep) const override {
        return this == samep;  // We don't compare members, require exact equivalence
    }
    virtual string name() const override { return m_name; }
    virtual void name(const string& flag) override { m_name = flag; }
    AstMemberDType* membersp() const {
        return VN_CAST(op1p(), MemberDType);
    }  // op1 = AstMember list
    void addMembersp(AstNode* nodep) { addNOp1p(nodep); }
    bool packed() const { return m_packed; }
    // packed() but as don't support unpacked, presently all structs
    static bool packedUnsup() { return true; }
    void isFourstate(bool flag) { m_isFourstate = flag; }
    virtual bool isFourstate() const override { return m_isFourstate; }
    void clearCache() { m_members.clear(); }
    void repairMemberCache();
    AstMemberDType* findMember(const string& name) const {
        const auto it = m_members.find(name);
        return (it == m_members.end()) ? nullptr : it->second;
    }
    static int lo() { return 0; }
    int hi() const { return dtypep()->width() - 1; }  // Packed classes look like arrays
    VNumRange declRange() const { return VNumRange{hi(), lo()}; }
};

class AstNodeArrayDType VL_NOT_FINAL : public AstNodeDType {
    // Array data type, ie "some_dtype var_name [2:0]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: RANGE (array bounds)
private:
    AstNodeDType* m_refDTypep = nullptr;  // Elements of this type (after widthing)
    AstNode* rangenp() const { return op2p(); }  // op2 = Array(s) of variable
protected:
    AstNodeArrayDType(AstType t, FileLine* fl)
        : AstNodeDType{t, fl} {}

public:
    ASTNODE_BASE_FUNCS(NodeArrayDType)
    virtual void dump(std::ostream& str) const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstNodeArrayDType* asamep = static_cast<const AstNodeArrayDType*>(samep);
        return (hi() == asamep->hi() && subDTypep() == asamep->subDTypep()
                && rangenp()->sameTree(asamep->rangenp()));
    }  // HashedDT doesn't recurse, so need to check children
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstNodeArrayDType* asamep = static_cast<const AstNodeArrayDType*>(samep);
        return (asamep && type() == samep->type() && hi() == asamep->hi()
                && rangenp()->sameTree(asamep->rangenp())
                && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp()));
    }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    AstRange* rangep() const { return VN_CAST(op2p(), Range); }  // op2 = Array(s) of variable
    void rangep(AstRange* nodep);
    // METHODS
    virtual AstBasicDType* basicp() const override {
        return subDTypep()->basicp();
    }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override {
        return elementsConst() * subDTypep()->widthTotalBytes();
    }
    int left() const;
    int right() const;
    int hi() const;
    int lo() const;
    int elementsConst() const;
    VNumRange declRange() const;
};

class AstNodeSel VL_NOT_FINAL : public AstNodeBiop {
    // Single bit range extraction, perhaps with non-constant selection or array selection
protected:
    AstNodeSel(AstType t, FileLine* fl, AstNode* fromp, AstNode* bitp)
        : AstNodeBiop{t, fl, fromp, bitp} {}

public:
    ASTNODE_BASE_FUNCS(NodeSel)
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* bitp() const { return op2p(); }  // op2 = Msb selection expression
    void bitp(AstNode* nodep) { setOp2p(nodep); }
    int bitConst() const;
    virtual bool hasDType() const override { return true; }
};

class AstNodeStream VL_NOT_FINAL : public AstNodeBiop {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
protected:
    AstNodeStream(AstType t, FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : AstNodeBiop{t, fl, lhsp, rhsp} {
        if (lhsp->dtypep()) dtypeSetLogicSized(lhsp->dtypep()->width(), VSigning::UNSIGNED);
    }

public:
    ASTNODE_BASE_FUNCS(NodeStream)
};

//######################################################################
// Tasks/functions common handling

class AstNodeCCall VL_NOT_FINAL : public AstNodeStmt {
    // A call of a C++ function, perhaps a AstCFunc or perhaps globally named
    // Functions are not statements, while tasks are. AstNodeStmt needs isStatement() to deal.
    AstCFunc* m_funcp;
    string m_selfPointer;  // Output code object pointer (e.g.: 'this')
    string m_classPrefix;  // Output class prefix (i.e.: the part before ::)
    string m_argTypes;

protected:
    AstNodeCCall(AstType t, FileLine* fl, AstCFunc* funcp, AstNode* argsp = nullptr)
        : AstNodeStmt{t, fl, true}
        , m_funcp{funcp} {
        addNOp2p(argsp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeCCall)
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual void cloneRelink() override;
    virtual const char* broken() const override;
    virtual int instrCount() const override { return instrCountCall(); }
    virtual bool same(const AstNode* samep) const override {
        const AstNodeCCall* asamep = static_cast<const AstNodeCCall*>(samep);
        return (funcp() == asamep->funcp() && argTypes() == asamep->argTypes());
    }
    AstNode* exprsp() const { return op2p(); }  // op2 = expressions to print
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override;
    virtual bool isOutputter() const override { return !isPure(); }
    AstCFunc* funcp() const { return m_funcp; }
    string selfPointer() const { return m_selfPointer; }
    void selfPointer(const string& value) { m_selfPointer = value; }
    string selfPointerProtect(bool useSelfForThis) const;
    string classPrefix() const { return m_classPrefix; }
    void classPrefix(const string& value) { m_classPrefix = value; }
    string classPrefixProtect() const;
    void argTypes(const string& str) { m_argTypes = str; }
    string argTypes() const { return m_argTypes; }
    // op1p reserved for AstCMethodCall
    AstNode* argsp() const { return op2p(); }
    void addArgsp(AstNode* nodep) { addOp2p(nodep); }
};

class AstNodeFTask VL_NOT_FINAL : public AstNode {
private:
    string m_name;  // Name of task
    string m_cname;  // Name of task if DPI import
    uint64_t m_dpiOpenParent = 0;  // DPI import open array, if !=0, how many callees
    bool m_taskPublic : 1;  // Public task
    bool m_attrIsolateAssign : 1;  // User isolate_assignments attribute
    bool m_classMethod : 1;  // Class method
    bool m_externProto : 1;  // Extern prototype
    bool m_externDef : 1;  // Extern definition
    bool m_prototype : 1;  // Just a prototype
    bool m_dpiExport : 1;  // DPI exported
    bool m_dpiImport : 1;  // DPI imported
    bool m_dpiContext : 1;  // DPI import context
    bool m_dpiOpenChild : 1;  // DPI import open array child wrapper
    bool m_dpiTask : 1;  // DPI import task (vs. void function)
    bool m_isConstructor : 1;  // Class constructor
    bool m_isHideLocal : 1;  // Verilog local
    bool m_isHideProtected : 1;  // Verilog protected
    bool m_pure : 1;  // DPI import pure (vs. virtual pure)
    bool m_pureVirtual : 1;  // Pure virtual
    bool m_virtual : 1;  // Virtual method in class
    VLifetime m_lifetime;  // Lifetime
protected:
    AstNodeFTask(AstType t, FileLine* fl, const string& name, AstNode* stmtsp)
        : AstNode{t, fl}
        , m_name{name}
        , m_taskPublic{false}
        , m_attrIsolateAssign{false}
        , m_classMethod{false}
        , m_externProto{false}
        , m_externDef{false}
        , m_prototype{false}
        , m_dpiExport{false}
        , m_dpiImport{false}
        , m_dpiContext{false}
        , m_dpiOpenChild{false}
        , m_dpiTask{false}
        , m_isConstructor{false}
        , m_isHideLocal{false}
        , m_isHideProtected{false}
        , m_pure{false}
        , m_pureVirtual{false}
        , m_virtual{false} {
        addNOp3p(stmtsp);
        cname(name);  // Might be overridden by dpi import/export
    }

public:
    ASTNODE_BASE_FUNCS(NodeFTask)
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool maybePointedTo() const override { return true; }
    virtual bool isGateOptimizable() const override {
        return !((m_dpiExport || m_dpiImport) && !m_pure);
    }
    // {AstFunc only} op1 = Range output variable
    virtual void name(const string& name) override { m_name = name; }
    string cname() const { return m_cname; }
    void cname(const string& cname) { m_cname = cname; }
    // op1 = Output variable (functions only, nullptr for tasks)
    AstNode* fvarp() const { return op1p(); }
    void addFvarp(AstNode* nodep) { addNOp1p(nodep); }
    bool isFunction() const { return fvarp() != nullptr; }
    // op2 = Class/package scope
    AstNode* classOrPackagep() const { return op2p(); }
    void classOrPackagep(AstNode* nodep) { setNOp2p(nodep); }
    // op3 = Statements/Ports/Vars
    AstNode* stmtsp() const { return op3p(); }  // op3 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp3p(nodep); }
    // op4 = scope name
    AstScopeName* scopeNamep() const { return VN_CAST(op4p(), ScopeName); }
    // MORE ACCESSORS
    void dpiOpenParentInc() { ++m_dpiOpenParent; }
    void dpiOpenParentClear() { m_dpiOpenParent = 0; }
    uint64_t dpiOpenParent() const { return m_dpiOpenParent; }
    void scopeNamep(AstNode* nodep) { setNOp4p(nodep); }
    void taskPublic(bool flag) { m_taskPublic = flag; }
    bool taskPublic() const { return m_taskPublic; }
    void attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    bool attrIsolateAssign() const { return m_attrIsolateAssign; }
    void classMethod(bool flag) { m_classMethod = flag; }
    bool classMethod() const { return m_classMethod; }
    void isExternProto(bool flag) { m_externProto = flag; }
    bool isExternProto() const { return m_externProto; }
    void isExternDef(bool flag) { m_externDef = flag; }
    bool isExternDef() const { return m_externDef; }
    void prototype(bool flag) { m_prototype = flag; }
    bool prototype() const { return m_prototype; }
    void dpiExport(bool flag) { m_dpiExport = flag; }
    bool dpiExport() const { return m_dpiExport; }
    void dpiImport(bool flag) { m_dpiImport = flag; }
    bool dpiImport() const { return m_dpiImport; }
    void dpiContext(bool flag) { m_dpiContext = flag; }
    bool dpiContext() const { return m_dpiContext; }
    void dpiOpenChild(bool flag) { m_dpiOpenChild = flag; }
    bool dpiOpenChild() const { return m_dpiOpenChild; }
    void dpiTask(bool flag) { m_dpiTask = flag; }
    bool dpiTask() const { return m_dpiTask; }
    void isConstructor(bool flag) { m_isConstructor = flag; }
    bool isConstructor() const { return m_isConstructor; }
    bool isHideLocal() const { return m_isHideLocal; }
    void isHideLocal(bool flag) { m_isHideLocal = flag; }
    bool isHideProtected() const { return m_isHideProtected; }
    void isHideProtected(bool flag) { m_isHideProtected = flag; }
    void pure(bool flag) { m_pure = flag; }
    bool pure() const { return m_pure; }
    void pureVirtual(bool flag) { m_pureVirtual = flag; }
    bool pureVirtual() const { return m_pureVirtual; }
    void isVirtual(bool flag) { m_virtual = flag; }
    bool isVirtual() const { return m_virtual; }
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
};

class AstNodeFTaskRef VL_NOT_FINAL : public AstNodeStmt {
    // A reference to a task (or function)
    // Functions are not statements, while tasks are. AstNodeStmt needs isStatement() to deal.
private:
    AstNodeFTask* m_taskp = nullptr;  // [AfterLink] Pointer to task referenced
    AstNodeModule* m_classOrPackagep = nullptr;  // Package hierarchy
    string m_name;  // Name of variable
    string m_dotted;  // Dotted part of scope the name()ed task/func is under or ""
    string m_inlinedDots;  // Dotted hierarchy flattened out
    bool m_pli = false;  // Pli system call ($name)
protected:
    AstNodeFTaskRef(AstType t, FileLine* fl, bool statement, AstNode* namep, AstNode* pinsp)
        : AstNodeStmt{t, fl, statement} {
        setOp1p(namep);
        addNOp3p(pinsp);
    }
    AstNodeFTaskRef(AstType t, FileLine* fl, bool statement, const string& name, AstNode* pinsp)
        : AstNodeStmt{t, fl, statement}
        , m_name{name} {
        addNOp3p(pinsp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeFTaskRef)
    virtual const char* broken() const override;
    virtual void cloneRelink() override {
        if (m_taskp && m_taskp->clonep()) m_taskp = m_taskp->clonep();
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool isGateOptimizable() const override {
        return m_taskp && m_taskp->isGateOptimizable();
    }
    string dotted() const { return m_dotted; }  // * = Scope name or ""
    string prettyDotted() const { return prettyName(dotted()); }
    string inlinedDots() const { return m_inlinedDots; }
    void inlinedDots(const string& flag) { m_inlinedDots = flag; }
    AstNodeFTask* taskp() const { return m_taskp; }  // [After Link] Pointer to variable
    void taskp(AstNodeFTask* taskp) { m_taskp = taskp; }
    virtual void name(const string& name) override { m_name = name; }
    void dotted(const string& name) { m_dotted = name; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    bool pli() const { return m_pli; }
    void pli(bool flag) { m_pli = flag; }
    // op1 = namep
    AstNode* namep() const { return op1p(); }
    // op2 = reserved for AstMethodCall
    // op3 = Pin interconnection list
    AstNode* pinsp() const { return op3p(); }
    void addPinsp(AstNode* nodep) { addOp3p(nodep); }
    // op4 = scope tracking
    AstScopeName* scopeNamep() const { return VN_CAST(op4p(), ScopeName); }
    void scopeNamep(AstNode* nodep) { setNOp4p(nodep); }
};

class AstNodeModule VL_NOT_FINAL : public AstNode {
    // A module, package, program or interface declaration;
    // something that can live directly under the TOP,
    // excluding $unit package stuff
private:
    string m_name;  // Name of the module
    string m_origName;  // Name of the module, ignoring name() changes, for dot lookup
    string m_hierName;  // Hierarchical name for errors, etc.
    bool m_modPublic : 1;  // Module has public references
    bool m_modTrace : 1;  // Tracing this module
    bool m_inLibrary : 1;  // From a library, no error if not used, never top level
    bool m_dead : 1;  // LinkDot believes is dead; will remove in Dead visitors
    bool m_hierBlock : 1;  // Hiearchical Block marked by HIER_BLOCK pragma
    bool m_internal : 1;  // Internally created
    bool m_recursive : 1;  // Recursive module
    bool m_recursiveClone : 1;  // If recursive, what module it clones, otherwise nullptr
    int m_level = 0;  // 1=top module, 2=cell off top module, ...
    int m_varNum = 0;  // Incrementing variable number
    int m_typeNum = 0;  // Incrementing implicit type number
    VLifetime m_lifetime;  // Lifetime
    VTimescale m_timeunit;  // Global time unit
    VOptionBool m_unconnectedDrive;  // State of `unconnected_drive
protected:
    AstNodeModule(AstType t, FileLine* fl, const string& name)
        : AstNode{t, fl}
        , m_name{name}
        , m_origName{name}
        , m_modPublic{false}
        , m_modTrace{false}
        , m_inLibrary{false}
        , m_dead{false}
        , m_hierBlock{false}
        , m_internal{false}
        , m_recursive{false}
        , m_recursiveClone{false} {}

public:
    ASTNODE_BASE_FUNCS(NodeModule)
    virtual void dump(std::ostream& str) const override;
    virtual bool maybePointedTo() const override { return true; }
    virtual string name() const override { return m_name; }
    virtual bool timescaleMatters() const = 0;
    AstNode* stmtsp() const { return op2p(); }  // op2 = List of statements
    AstActive* activesp() const { return VN_CAST(op3p(), Active); }  // op3 = List of i/sblocks
    // METHODS
    void addInlinesp(AstNode* nodep) { addOp1p(nodep); }
    void addStmtp(AstNode* nodep) { addNOp2p(nodep); }
    void addActivep(AstNode* nodep) { addOp3p(nodep); }
    // ACCESSORS
    virtual void name(const string& name) override { m_name = name; }
    virtual string origName() const override { return m_origName; }
    string hierName() const { return m_hierName; }
    void hierName(const string& hierName) { m_hierName = hierName; }
    bool inLibrary() const { return m_inLibrary; }
    void inLibrary(bool flag) { m_inLibrary = flag; }
    void level(int level) { m_level = level; }
    int level() const { return m_level; }
    bool isTop() const { return level() == 1; }
    int varNumGetInc() { return ++m_varNum; }
    int typeNumGetInc() { return ++m_typeNum; }
    void modPublic(bool flag) { m_modPublic = flag; }
    bool modPublic() const { return m_modPublic; }
    void modTrace(bool flag) { m_modTrace = flag; }
    bool modTrace() const { return m_modTrace; }
    void dead(bool flag) { m_dead = flag; }
    bool dead() const { return m_dead; }
    void hierBlock(bool flag) { m_hierBlock = flag; }
    bool hierBlock() const { return m_hierBlock; }
    void internal(bool flag) { m_internal = flag; }
    bool internal() const { return m_internal; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
    void recursiveClone(bool flag) { m_recursiveClone = flag; }
    bool recursiveClone() const { return m_recursiveClone; }
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
    void unconnectedDrive(const VOptionBool flag) { m_unconnectedDrive = flag; }
    VOptionBool unconnectedDrive() const { return m_unconnectedDrive; }
};

class AstNodeRange VL_NOT_FINAL : public AstNode {
    // A range, sized or unsized
protected:
    AstNodeRange(AstType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTNODE_BASE_FUNCS(NodeRange)
    virtual void dump(std::ostream& str) const override;
};

//######################################################################
// Inline AstNVisitor METHODS

inline void AstNVisitor::iterate(AstNode* nodep) { nodep->accept(*this); }
inline void AstNVisitor::iterateNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->accept(*this);
}
inline void AstNVisitor::iterateChildren(AstNode* nodep) { nodep->iterateChildren(*this); }
inline void AstNVisitor::iterateChildrenBackwards(AstNode* nodep) {
    nodep->iterateChildrenBackwards(*this);
}
inline void AstNVisitor::iterateChildrenConst(AstNode* nodep) {
    nodep->iterateChildrenConst(*this);
}
inline void AstNVisitor::iterateAndNextNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->iterateAndNext(*this);
}
inline void AstNVisitor::iterateAndNextConstNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->iterateAndNextConst(*this);
}
inline AstNode* AstNVisitor::iterateSubtreeReturnEdits(AstNode* nodep) {
    return nodep->iterateSubtreeReturnEdits(*this);
}

//######################################################################

#include "V3AstNodes.h"

#endif  // Guard
