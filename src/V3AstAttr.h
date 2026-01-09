// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode attributes and sub-types
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// This files contains small classes that contain attributes or enum classes
// used by V3AstNode*.h.  Classes that are part of the base AST structure
// belong in V3Ast.h instead.
//
// The classes in this file should kept in mostly sorted order, with
// a few earlier-definition dependent exception at the end.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTATTR_H_
#define VERILATOR_V3ASTATTR_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// Hint class so we can choose constructors
class VFlagBitPacked {};
class VFlagChildDType {};  // Used by parser.y to select constructor that sets childDType
class VFlagLogicPacked {};

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
        static const char* const names[] = {"[RV] <-", "[LV] =>", "[LRV] <=>", "--"};
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

//######################################################################

class VAlwaysKwd final {
public:
    enum en : uint8_t { ALWAYS, ALWAYS_FF, ALWAYS_LATCH, ALWAYS_COMB, CONT_ASSIGN };
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
        static const char* const names[]
            = {"always", "always_ff", "always_latch", "always_comb", "cont_assign"};
        return names[m_e];
    }
};
constexpr bool operator==(const VAlwaysKwd& lhs, const VAlwaysKwd& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VAlwaysKwd& lhs, VAlwaysKwd::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VAlwaysKwd::en lhs, const VAlwaysKwd& rhs) { return lhs == rhs.m_e; }

// ######################################################################

class VAssertCtlType final {
public:
    // IEEE 1800-2023 Table 20-5
    enum en : uint8_t {
        _TO_BE_EVALUATED = 0,
        LOCK = 1,
        UNLOCK = 2,
        ON = 3,
        OFF = 4,
        KILL = 5,
        PASS_ON = 6,
        PASS_OFF = 7,
        FAIL_ON = 8,
        FAIL_OFF = 9,
        NONVACUOUS_ON = 10,
        VACUOUS_OFF = 11
    };
    enum en m_e;
    VAssertCtlType()
        : m_e{_TO_BE_EVALUATED} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VAssertCtlType(en _e)
        : m_e{_e} {}
    explicit VAssertCtlType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        // IEEE 1800-2023 20.11
        static const char* const names[] = {"",
                                            "",
                                            "",
                                            "$asserton",
                                            "$assertoff",
                                            "$assertkill",
                                            "$assertpasson",
                                            "$assertpassoff",
                                            "$assertfailon",
                                            "$assertfailoff",
                                            "$assertnonvacuouson",
                                            "$assertvacuousoff"};
        return names[m_e];
    }
};
constexpr bool operator==(const VAssertCtlType& lhs, const VAssertCtlType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VAssertCtlType& lhs, VAssertCtlType::en rhs) {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VAssertCtlType::en lhs, const VAssertCtlType& rhs) {
    return lhs == rhs.m_e;
}

// ######################################################################

class VAssertDirectiveType final {
public:
    // IEEE 1800-2023 Table 20-7
    enum en : uint8_t {
        INTERNAL = 0,  // Non IEEE type, for directives to be evaluated from expression.
        ASSERT = (1 << 0),
        COVER = (1 << 1),
        ASSUME = (1 << 2),
        VIOLATION_CASE = (1 << 3),  // Non IEEE type, for case constructs
                                    // with unique, unique0 or priority pragmas.
        VIOLATION_IF = (1 << 4),  // Non IEEE type, for if constructs
                                  // with unique, unique0 or priority pragmas.
        INTRINSIC = (1 << 5),  // Non IEEE type, for intrinsic assertions.
        RESTRICT = (1 << 6),  // Non IEEE type, for ignored restrict assertions.
    };
    enum en m_e;
    VAssertDirectiveType()
        : m_e{ASSERT} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VAssertDirectiveType(en _e)
        : m_e{_e} {}
    explicit VAssertDirectiveType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    string ascii() const {
        std::stringstream types;
        if (m_e == INTERNAL)
            types << "INTERNAL ";
        else {
            if (m_e & ASSERT) types << "ASSERT ";
            if (m_e & COVER) types << "COVER ";
            if (m_e & ASSUME) types << "ASSUME ";
            if (m_e & VIOLATION_CASE) types << "VIOLATION_CASE ";
            if (m_e & VIOLATION_IF) types << "VIOLATION_IF ";
            if (m_e & INTRINSIC) types << "INTRINSIC ";
            if (m_e & RESTRICT) types << "RESTRICT ";
        }
        const string str = types.str();
        UASSERT(!str.empty(), "Assert should be of one of types");
        return str.substr(0, str.size() - 1);
    }
    constexpr operator en() const { return m_e; }
};
constexpr bool operator==(const VAssertDirectiveType& lhs, const VAssertDirectiveType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VAssertDirectiveType& lhs, VAssertDirectiveType::en rhs) {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VAssertDirectiveType::en lhs, const VAssertDirectiveType& rhs) {
    return lhs == rhs.m_e;
}
constexpr VAssertDirectiveType::en operator|(VAssertDirectiveType::en lhs,
                                             VAssertDirectiveType::en rhs) {
    return VAssertDirectiveType::en(static_cast<uint8_t>(lhs) | static_cast<uint8_t>(rhs));
}

// ######################################################################

class VAssertType final {
public:
    // IEEE 1800-2023 Table 20-6
    enum en : uint8_t {
        INTERNAL = 0,  // Non IEEE type, for assertions that should not be controlled.
        CONCURRENT = (1 << 0),
        SIMPLE_IMMEDIATE = (1 << 1),
        OBSERVED_DEFERRED_IMMEDIATE = (1 << 2),
        FINAL_DEFERRED_IMMEDIATE = (1 << 3),
        EXPECT = (1 << 4),
        UNIQUE = (1 << 5),
        UNIQUE0 = (1 << 6),
        PRIORITY = (1 << 7),
    };
    enum en m_e;
    VAssertType()
        : m_e{INTERNAL} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VAssertType(en _e)
        : m_e{_e} {}
    explicit VAssertType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    bool containsAny(VAssertType other) const { return m_e & other.m_e; }
    string ascii() const {
        std::stringstream types;
        if (m_e == INTERNAL)
            types << "INTERNAL ";
        else {
            if (m_e & CONCURRENT) types << "CONCURRENT ";
            if (m_e & SIMPLE_IMMEDIATE) types << "SIMPLE_IMMEDIATE ";
            if (m_e & OBSERVED_DEFERRED_IMMEDIATE) types << "OBSERVED_DEFERRED_IMMEDIATE ";
            if (m_e & FINAL_DEFERRED_IMMEDIATE) types << "FINAL_DEFERRED_IMMEDIATE ";
            if (m_e & EXPECT) types << "EXPECT ";
            if (m_e & UNIQUE) types << "UNIQUE ";
            if (m_e & UNIQUE0) types << "UNIQUE0 ";
            if (m_e & PRIORITY) types << "PRIORITY ";
        }
        const string str = types.str();
        UASSERT(!str.empty(), "Assert should be of one of types");
        return str.substr(0, str.size() - 1);
    }
    constexpr operator en() const { return m_e; }
};
constexpr bool operator==(const VAssertType& lhs, const VAssertType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VAssertType& lhs, VAssertType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VAssertType::en lhs, const VAssertType& rhs) { return lhs == rhs.m_e; }
constexpr VAssertType::en operator|(VAssertType::en lhs, VAssertType::en rhs) {
    return VAssertType::en(static_cast<uint8_t>(lhs) | static_cast<uint8_t>(rhs));
}

// ######################################################################

class VAttrType final {
public:
    // clang-format off
    enum en: uint8_t  {
        ILLEGAL,
        //
        DIM_BITS,                       // V3Const converts to constant
        DIM_BITS_OR_NUMBER,             // V3Const converts to constant
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
        ENUM_FIRST,                     // V3Width processes
        ENUM_LAST,                      // V3Width processes
        ENUM_NUM,                       // V3Width processes
        ENUM_NEXT,                      // V3Width processes
        ENUM_PREV,                      // V3Width processes
        ENUM_NAME,                      // V3Width processes
        ENUM_VALID,                     // V3Width processes
        //
        FUNC_ARG_PROTO,                 // V3WidthCommit processes
        FUNC_RETURN_PROTO,              // V3WidthCommit processes
        //
        TYPEID,                         // V3Width processes
        TYPENAME,                       // V3Width processes
        //
        VAR_BASE,                       // V3LinkResolve creates for AstPreSel, V3LinkParam removes
        VAR_FORCEABLE,                  // V3LinkParse moves to AstVar::isForceable
        VAR_PORT_DTYPE,                 // V3LinkDot for V3Width to check port dtype
        VAR_PUBLIC,                     // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT,                // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT_RD,             // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT_RW,             // V3LinkParse moves to AstVar::sigPublic
        VAR_ISOLATE_ASSIGNMENTS,        // V3LinkParse moves to AstVar::attrIsolateAssign
        VAR_SC_BIGUINT,                 // V3LinkParse moves to AstVar::attrScBigUint
        VAR_SC_BV,                      // V3LinkParse moves to AstVar::attrScBv
        VAR_SFORMAT,                    // V3LinkParse moves to AstVar::attrSFormat
        VAR_SPLIT_VAR                   // V3LinkParse moves to AstVar::attrSplitVar
    };
    // clang-format on
    enum en m_e;
    const char* ascii() const {
        // clang-format off
        static const char* const names[] = {
            "%E-AT",
            "DIM_BITS", "DIM_BITS_OR_NUMBER", "DIM_DIMENSIONS",
            "DIM_HIGH", "DIM_INCREMENT", "DIM_LEFT",
            "DIM_LOW", "DIM_RIGHT", "DIM_SIZE", "DIM_UNPK_DIMENSIONS",
            "DT_PUBLIC",
            "ENUM_FIRST", "ENUM_LAST", "ENUM_NUM",
            "ENUM_NEXT", "ENUM_PREV", "ENUM_NAME", "ENUM_VALID",
            "FUNC_ARG_PROTO", "FUNC_RETURN_PROTO",
            "TYPEID", "TYPENAME",
            "VAR_BASE", "VAR_FORCEABLE", "VAR_PORT_DTYPE", "VAR_PUBLIC",
            "VAR_PUBLIC_FLAT", "VAR_PUBLIC_FLAT_RD", "VAR_PUBLIC_FLAT_RW",
            "VAR_ISOLATE_ASSIGNMENTS", "VAR_SC_BIGUINT", "VAR_SC_BV", "VAR_SFORMAT",
            "VAR_SPLIT_VAR"
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

class VBaseOverride final {
    bool m_extends : 1;
    bool m_final : 1;
    bool m_initial : 1;

public:
    VBaseOverride()
        : m_extends{false}
        , m_final{false}
        , m_initial{false} {}
    class Extends {};
    explicit VBaseOverride(Extends)
        : m_extends{true}
        , m_final{false}
        , m_initial{false} {}
    class Final {};
    explicit VBaseOverride(Final)
        : m_extends{false}
        , m_final{true}
        , m_initial{false} {}
    class Initial {};
    explicit VBaseOverride(Initial)
        : m_extends{false}
        , m_final{false}
        , m_initial{true} {}
    void combine(const VBaseOverride& other) {
        m_extends |= other.m_extends;
        m_final |= other.m_final;
        m_initial |= other.m_initial;
    }
    bool isAny() const { return m_extends | m_final | m_initial; }
    bool isExtends() const { return m_extends; }
    bool isFinal() const { return m_final; }
    bool isInitial() const { return m_initial; }
    string ascii() const {
        string out;
        if (m_initial) out = VString::dot(out, " ", "initial");
        if (m_extends) out = VString::dot(out, " ", "extends");
        if (m_final) out = VString::dot(out, " ", "final");
        return out;
    }
};

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
        // Property / Sequence argument type
        UNTYPED,
        // Internal types for mid-steps
        SCOPEPTR,
        CHARPTR,
        MTASKSTATE,
        DELAY_SCHEDULER,
        TRIGGER_SCHEDULER,
        DYNAMIC_TRIGGER_SCHEDULER,
        FORK_SYNC,
        PROCESS_REFERENCE,
        RANDOM_GENERATOR,
        RANDOM_STDGENERATOR,
        // Unsigned and two state; fundamental types
        UINT32,
        UINT64,
        // Internal types, eliminated after parsing
        LOGIC_IMPLICIT,
        // Leave last
        _ENUM_MAX
    };
    enum en m_e;
    const char* ascii() const VL_MT_SAFE {
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
                                            "untyped",
                                            "VerilatedScope*",
                                            "char*",
                                            "VlMTaskState",
                                            "VlDelayScheduler",
                                            "VlTriggerScheduler",
                                            "VlDynamicTriggerScheduler",
                                            "VlFork",
                                            "VlProcessRef",
                                            "VlRandomizer",
                                            "VlStdRandomizer",
                                            "IData",
                                            "QData",
                                            "LOGIC_IMPLICIT",
                                            " MAX"};
        return names[m_e];
    }
    const char* dpiType() const {
        static const char* const names[]
            = {"%E-unk",      "svBit",           "char",         "void*",          "char",
               "int",         "%E-integer",      "svLogic",      "long long",      "double",
               "short",       "%E-time",         "const char*",  "%E-untyped",     "dpiScope",
               "const char*", "%E-mtaskstate",   "%E-dly-sched", "%E-trig-sched",  "%E-dyn-sched",
               "%E-fork",     "%E-proc-ref",     "%E-rand-gen",  "%E-stdrand-gen", "IData",
               "QData",       "%E-logic-implct", " MAX"};
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
        case DELAY_SCHEDULER: return 0;  // opaque
        case TRIGGER_SCHEDULER: return 0;  // opaque
        case DYNAMIC_TRIGGER_SCHEDULER: return 0;  // opaque
        case FORK_SYNC: return 0;  // opaque
        case PROCESS_REFERENCE: return 0;  // opaque
        case RANDOM_GENERATOR: return 0;  // opaque
        case RANDOM_STDGENERATOR: return 0;  // opaque
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
                || m_e == LONGINT || m_e == SHORTINT || m_e == UINT32 || m_e == UINT64
                || m_e == TIME);
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
                || m_e == MTASKSTATE || m_e == DELAY_SCHEDULER || m_e == TRIGGER_SCHEDULER
                || m_e == DYNAMIC_TRIGGER_SCHEDULER || m_e == FORK_SYNC || m_e == PROCESS_REFERENCE
                || m_e == RANDOM_GENERATOR || m_e == RANDOM_STDGENERATOR || m_e == DOUBLE
                || m_e == UNTYPED);
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

    const char* traceSigType() const {
        // VerilatedTraceSigType to used in trace signal declaration
        static const char* const lut[] = {
            /* UNKNOWN:                   */ "",  // Should not be traced
            /* BIT:                       */ "BIT",
            /* BYTE:                      */ "BYTE",
            /* CHANDLE:                   */ "LONGINT",
            /* EVENT:                     */ "EVENT",
            /* INT:                       */ "INT",
            /* INTEGER:                   */ "INTEGER",
            /* LOGIC:                     */ "LOGIC",
            /* LONGINT:                   */ "LONGINT",
            /* DOUBLE:                    */ "DOUBLE",
            /* SHORTINT:                  */ "SHORTINT",
            /* TIME:                      */ "TIME",
            /* STRING:                    */ "",
            /* UNTYPED:                   */ "",  // Should not be traced
            /* SCOPEPTR:                  */ "",  // Should not be traced
            /* CHARPTR:                   */ "",  // Should not be traced
            /* MTASKSTATE:                */ "",  // Should not be traced
            /* DELAY_SCHEDULER:           */ "",  // Should not be traced
            /* TRIGGER_SCHEDULER:         */ "",  // Should not be traced
            /* DYNAMIC_TRIGGER_SCHEDULER: */ "",  // Should not be traced
            /* FORK_SYNC:                 */ "",  // Should not be traced
            /* PROCESS_REFERENCE:         */ "",  // Should not be traced
            /* RANDOM_GENERATOR:          */ "",  // Should not be traced
            /* RANDOM_STD_GENERATOR:      */ "",  // Should not be traced
            /* UINT32:                    */ "BIT",
            /* UINT64:                    */ "BIT",
            /* LOGIC_IMPLICIT:            */ "",  // Should not be traced
        };
        return lut[m_e];
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

class VCMethod final {
public:
    // Entries in this table need to match below VCMethod::s_itemData[] table
    enum en : uint8_t {
        _NONE,  // Unknown
        ARRAY_AND,
        ARRAY_AT,
        ARRAY_AT_BACK,
        ARRAY_AT_WRITE,
        ARRAY_FIND,
        ARRAY_FIND_FIRST,
        ARRAY_FIND_FIRST_INDEX,
        ARRAY_FIND_INDEX,
        ARRAY_FIND_LAST,
        ARRAY_FIND_LAST_INDEX,
        ARRAY_FIRST,
        ARRAY_INSIDE,
        ARRAY_LAST,
        ARRAY_MAX,
        ARRAY_MIN,
        ARRAY_NEXT,
        ARRAY_OR,
        ARRAY_POP_BACK,
        ARRAY_POP_FRONT,
        ARRAY_PREV,
        ARRAY_PRODUCT,
        ARRAY_PUSH_BACK,
        ARRAY_PUSH_FRONT,
        ARRAY_REVERSE,
        ARRAY_RSORT,
        ARRAY_R_AND,
        ARRAY_R_OR,
        ARRAY_R_PRODUCT,
        ARRAY_R_SUM,
        ARRAY_R_XOR,
        ARRAY_SHUFFLE,
        ARRAY_SORT,
        ARRAY_SUM,
        ARRAY_UNIQUE,
        ARRAY_UNIQUE_INDEX,
        ARRAY_XOR,
        ASSOC_CLEAR,
        ASSOC_ERASE,
        ASSOC_EXISTS,
        ASSOC_FIRST,
        ASSOC_NEXT,
        ASSOC_SIZE,
        CLASS_SET_RANDMODE,
        DYN_AT_WRITE_APPEND,
        DYN_AT_WRITE_APPEND_BACK,
        DYN_CLEAR,
        DYN_ERASE,
        DYN_INSERT,
        DYN_POP,
        DYN_POP_FRONT,
        DYN_PUSH,
        DYN_PUSH_FRONT,
        DYN_RENEW,
        DYN_RENEW_COPY,
        DYN_RESIZE,
        DYN_SIZE,
        DYN_SLICE,
        DYN_SLICE_BACK_BACK,
        DYN_SLICE_FRONT_BACK,
        EVENT_CLEAR_FIRED,
        EVENT_CLEAR_TRIGGERED,
        EVENT_FIRE,
        EVENT_IS_FIRED,
        EVENT_IS_TRIGGERED,
        FORK_DONE,
        FORK_INIT,
        FORK_JOIN,
        RANDOMIZER_BASIC_STD_RANDOMIZATION,
        RANDOMIZER_CLEARCONSTRAINTS,
        RANDOMIZER_CLEARALL,
        RANDOMIZER_HARD,
        RANDOMIZER_SOFT,
        RANDOMIZER_WRITE_VAR,
        RNG_GET_RANDSTATE,
        RNG_SET_RANDSTATE,
        SCHED_ANY_TRIGGERED,
        SCHED_AWAITING_CURRENT_TIME,
        SCHED_COMMIT,
        SCHED_DELAY,
        SCHED_DO_POST_UPDATES,
        SCHED_ENQUEUE,
        SCHED_EVALUATE,
        SCHED_EVALUATION,
        SCHED_POST_UPDATE,
        SCHED_RESUME,
        SCHED_RESUMPTION,
        SCHED_TRIGGER,
        UNPACKED_ASSIGN,
        UNPACKED_FILL,
        UNPACKED_NEQ,
        _ENUM_MAX  // Leave last
    };

private:
    struct Item final {
        enum en m_e;  // Method's enum mnemonic, for checking
        const char* m_name;  // Method name, printed into C++
        bool m_pure;  // Method being called is pure
    };
    static Item s_itemData[];

public:
    enum en m_e;
    VCMethod()
        : m_e{_NONE} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VCMethod(en _e)
        : m_e{_e} {}
    explicit VCMethod(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const VL_PURE { return s_itemData[m_e].m_name; }
    bool isPure() const VL_PURE { return s_itemData[m_e].m_pure; }
    // Return array method for given name
    static VCMethod arrayMethod(const string& name);
    static void selfTest();
};
constexpr bool operator==(const VCMethod& lhs, const VCMethod& rhs) { return lhs.m_e == rhs.m_e; }
constexpr bool operator==(const VCMethod& lhs, VCMethod::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VCMethod::en lhs, const VCMethod& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VCMethod& rhs) {
    return os << rhs.ascii();
}

// Entries in this table need to match above VCMethod enum table
//
// {Mnemonic, C++ method, pure}
#define V3AST_VCMETHOD_ITEMDATA_DECL \
    VCMethod::Item VCMethod::s_itemData[] \
        = {{_NONE, "_none", false}, \
           {ARRAY_AND, "and", true}, \
           {ARRAY_AT, "at", true}, \
           {ARRAY_AT_BACK, "atBack", true}, \
           {ARRAY_AT_WRITE, "atWrite", true}, \
           {ARRAY_FIND, "find", true}, \
           {ARRAY_FIND_FIRST, "find_first", true}, \
           {ARRAY_FIND_FIRST_INDEX, "find_first_index", true}, \
           {ARRAY_FIND_INDEX, "find_index", true}, \
           {ARRAY_FIND_LAST, "find_last", true}, \
           {ARRAY_FIND_LAST_INDEX, "find_last_index", true}, \
           {ARRAY_FIRST, "first", false}, \
           {ARRAY_INSIDE, "inside", true}, \
           {ARRAY_LAST, "last", false}, \
           {ARRAY_MAX, "max", true}, \
           {ARRAY_MIN, "min", true}, \
           {ARRAY_NEXT, "next", false}, \
           {ARRAY_OR, "or", true}, \
           {ARRAY_POP_BACK, "pop_back", false}, \
           {ARRAY_POP_FRONT, "pop_front", false}, \
           {ARRAY_PREV, "prev", false}, \
           {ARRAY_PRODUCT, "product", true}, \
           {ARRAY_PUSH_BACK, "push_back", false}, \
           {ARRAY_PUSH_FRONT, "push_front", false}, \
           {ARRAY_REVERSE, "reverse", false}, \
           {ARRAY_RSORT, "rsort", false}, \
           {ARRAY_R_AND, "r_and", true}, \
           {ARRAY_R_OR, "r_or", true}, \
           {ARRAY_R_PRODUCT, "r_product", true}, \
           {ARRAY_R_SUM, "r_sum", true}, \
           {ARRAY_R_XOR, "r_xor", true}, \
           {ARRAY_SHUFFLE, "shuffle", false}, \
           {ARRAY_SORT, "sort", false}, \
           {ARRAY_SUM, "sum", true}, \
           {ARRAY_UNIQUE, "unique", true}, \
           {ARRAY_UNIQUE_INDEX, "unique_index", true}, \
           {ARRAY_XOR, "xor", true}, \
           {ASSOC_CLEAR, "clear", false}, \
           {ASSOC_ERASE, "erase", false}, \
           {ASSOC_EXISTS, "exists", true}, \
           {ASSOC_FIRST, "first", false}, \
           {ASSOC_NEXT, "next", false}, \
           {ASSOC_SIZE, "size", true}, \
           {CLASS_SET_RANDMODE, "set_randmode", false}, \
           {DYN_AT_WRITE_APPEND, "atWriteAppend", false}, \
           {DYN_AT_WRITE_APPEND_BACK, "atWriteAppendBack", false}, \
           {DYN_CLEAR, "clear", false}, \
           {DYN_ERASE, "erase", false}, \
           {DYN_INSERT, "insert", false}, \
           {DYN_POP, "pop", false}, \
           {DYN_POP_FRONT, "pop_front", false}, \
           {DYN_PUSH, "push", false}, \
           {DYN_PUSH_FRONT, "push_front", false}, \
           {DYN_RENEW, "renew", false}, \
           {DYN_RENEW_COPY, "renew_copy", false}, \
           {DYN_RESIZE, "resize", false}, \
           {DYN_SIZE, "size", true}, \
           {DYN_SLICE, "slice", true}, \
           {DYN_SLICE_BACK_BACK, "sliceBackBack", true}, \
           {DYN_SLICE_FRONT_BACK, "sliceFrontBack", true}, \
           {EVENT_CLEAR_FIRED, "clearFired", false}, \
           {EVENT_CLEAR_TRIGGERED, "clearTriggered", false}, \
           {EVENT_FIRE, "fire", false}, \
           {EVENT_IS_FIRED, "isFired", true}, \
           {EVENT_IS_TRIGGERED, "isTriggered", true}, \
           {FORK_DONE, "done", false}, \
           {FORK_INIT, "init", false}, \
           {FORK_JOIN, "join", false}, \
           {RANDOMIZER_BASIC_STD_RANDOMIZATION, "basicStdRandomization", false}, \
           {RANDOMIZER_CLEARCONSTRAINTS, "clearConstraints", false}, \
           {RANDOMIZER_CLEARALL, "clearAll", false}, \
           {RANDOMIZER_HARD, "hard", false}, \
           {RANDOMIZER_SOFT, "soft", false}, \
           {RANDOMIZER_WRITE_VAR, "write_var", false}, \
           {RNG_GET_RANDSTATE, "__Vm_rng.get_randstate", true}, \
           {RNG_SET_RANDSTATE, "__Vm_rng.set_randstate", false}, \
           {SCHED_ANY_TRIGGERED, "anyTriggered", false}, \
           {SCHED_AWAITING_CURRENT_TIME, "awaitingCurrentTime", true}, \
           {SCHED_COMMIT, "commit", false}, \
           {SCHED_DELAY, "delay", false}, \
           {SCHED_DO_POST_UPDATES, "doPostUpdates", false}, \
           {SCHED_ENQUEUE, "enqueue", false}, \
           {SCHED_EVALUATE, "evaluate", false}, \
           {SCHED_EVALUATION, "evaluation", false}, \
           {SCHED_POST_UPDATE, "postUpdate", false}, \
           {SCHED_RESUME, "resume", false}, \
           {SCHED_RESUMPTION, "resumption", false}, \
           {SCHED_TRIGGER, "trigger", false}, \
           {UNPACKED_ASSIGN, "assign", false}, \
           {UNPACKED_FILL, "fill", false}, \
           {UNPACKED_NEQ, "neq", true}, \
           {_ENUM_MAX, "_ENUM_MAX", false}};

// ######################################################################

class VCaseType final {
public:
    enum en : uint8_t { CT_CASE, CT_CASEX, CT_CASEZ, CT_CASEINSIDE, CT_RANDSEQUENCE };
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

class VCastable final {
public:
    enum en : uint8_t {
        UNSUPPORTED,
        SAMEISH,
        COMPATIBLE,
        ENUM_EXPLICIT,
        ENUM_IMPLICIT,
        DYNAMIC_CLASS,
        INCOMPATIBLE,
        _ENUM_MAX  // Leave last
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[]
            = {"UNSUPPORTED",   "SAMEISH",       "COMPATIBLE",  "ENUM_EXPLICIT",
               "ENUM_IMPLICIT", "DYNAMIC_CLASS", "INCOMPATIBLE"};
        return names[m_e];
    }
    bool isAssignable() const { return m_e != UNSUPPORTED && m_e != INCOMPATIBLE; }
    VCastable()
        : m_e{UNSUPPORTED} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VCastable(en _e)
        : m_e{_e} {}
    explicit VCastable(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
};
constexpr bool operator==(const VCastable& lhs, const VCastable& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VCastable& lhs, VCastable::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VCastable::en lhs, const VCastable& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VCastable& rhs) {
    return os << rhs.ascii();
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
    string prettyName() const { return verilogKwd(); }
    bool isAny() const { return m_e != NONE; }
    bool isInout() const { return m_e == INOUT; }
    bool isInoutOrRef() const { return m_e == INOUT || m_e == REF || m_e == CONSTREF; }
    bool isInput() const { return m_e == INPUT; }
    bool isNonOutput() const {
        return m_e == INPUT || m_e == INOUT || m_e == REF || m_e == CONSTREF;
    }
    bool isReadOnly() const VL_MT_SAFE { return m_e == INPUT || m_e == CONSTREF; }
    bool isWritable() const VL_MT_SAFE { return m_e == OUTPUT || m_e == INOUT || m_e == REF; }
    bool isRef() const VL_MT_SAFE { return m_e == REF; }
    bool isConstRef() const VL_MT_SAFE { return m_e == CONSTREF; }
};
constexpr bool operator==(const VDirection& lhs, const VDirection& rhs) VL_MT_SAFE {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VDirection& lhs, VDirection::en rhs) VL_MT_SAFE {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VDirection::en lhs, const VDirection& rhs) VL_MT_SAFE {
    return lhs == rhs.m_e;
}
inline std::ostream& operator<<(std::ostream& os, const VDirection& rhs) {
    return os << rhs.ascii();
}

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

class VEdgeType final {
public:
    // REMEMBER to edit the strings below too
    enum en : uint8_t {
        // These must be in general -> most specific order, as we sort by it
        // in V3Const::visit AstSenTree
        // Involving a variable
        ET_CHANGED,  // Value changed
        ET_BOTHEDGE,  // POSEDGE | NEGEDGE (i.e.: 'edge' in Verilog)
        ET_POSEDGE,
        ET_NEGEDGE,
        ET_EVENT,  // VlEventBase::isFired
        // Involving an expression
        ET_TRUE,
        //
        ET_COMBO,  // Sensitive to all combo inputs to this block
        ET_COMBO_STAR,  // Sensitive to all combo inputs to this block (from .*)
        ET_HYBRID,  // This is like ET_COMB, but with explicit sensitivity to an expression
        ET_STATIC,  // static variable initializers (runs before 'initial')
        ET_INITIAL,  // 'initial' statements
        ET_FINAL,  // 'final' statements
        ET_NEVER  // Never occurs (optimized away)
    };
    enum en m_e;
    bool clockedStmt() const {
        static const bool clocked[] = {
            true,  // ET_CHANGED
            true,  // ET_BOTHEDGE
            true,  // ET_POSEDGE
            true,  // ET_NEGEDGE
            true,  // ET_EVENT
            true,  // ET_TRUE

            false,  // ET_COMBO
            false,  // ET_COMBO_STAR
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
        default: UASSERT_STATIC(0, "Inverting bad edgeType()"); return ET_NEGEDGE;
        }
    }
    const char* ascii() const {
        static const char* const names[]
            = {"CHANGED",    "BOTH",   "POS",    "NEG",     "EVENT", "TRUE", "COMBO",
               "COMBO_STAR", "HYBRID", "STATIC", "INITIAL", "FINAL", "NEVER"};
        return names[m_e];
    }
    const char* verilogKwd() const {
        static const char* const names[]
            = {"[changed]", "edge",     "posedge",  "negedge",   "[event]", "[true]", "*",
               "*",         "[hybrid]", "[static]", "[initial]", "[final]", "[never]"};
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

class VFwdType final {
public:
    enum en : uint8_t { NONE, ENUM, STRUCT, UNION, CLASS, INTERFACE_CLASS, GENERIC_INTERFACE };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[]
            = {"none", "enum", "struct", "union", "class", "interface class", "generic interface"};
        return names[m_e];
    }
    VFwdType()
        : m_e{NONE} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VFwdType(en _e)
        : m_e{_e} {}
    explicit VFwdType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    // Is a node type compatible with the declaration
    bool isNodeCompatible(const AstNode* nodep) const;
};
constexpr bool operator==(const VFwdType& lhs, const VFwdType& rhs) { return lhs.m_e == rhs.m_e; }
constexpr bool operator==(const VFwdType& lhs, VFwdType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VFwdType::en lhs, const VFwdType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VFwdType& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

class VIsCached final {
    // Used in some nodes to cache results of boolean methods
    // If cachedCnt == 0, not cached
    // else if cachedCnt == s_cachedCntGbl, then m_state is if cached
    uint64_t m_cachedCnt : 63;  // Mark of when cache was computed
    uint64_t m_state : 1;
    static uint64_t s_cachedCntGbl;  // Global computed count

public:
    VIsCached()
        : m_cachedCnt{0}
        , m_state{0} {}
    bool isCached() const { return m_cachedCnt == s_cachedCntGbl; }
    bool get() const { return m_state; }
    void set(bool flag) {
        m_cachedCnt = s_cachedCntGbl;
        m_state = flag;
    }
    void clearCache() {
        m_cachedCnt = 0;
        m_state = 0;
    }
    static void clearCacheTree() {
        ++s_cachedCntGbl;
        // 64 bits so won't overflow
        // UASSERT_STATIC(s_cachedCntGbl < MAX_CNT, "Overflow of cache counting");
    }
};

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
    constexpr operator en() const { return m_e; }
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

class VLifetime final {
public:
    enum en : uint8_t {
        NONE,
        AUTOMATIC_EXPLICIT,  // Automatic assigned by user
        AUTOMATIC_IMPLICIT,  // AUtomatic propagated from above
        STATIC_EXPLICIT,  // Static assigned by user
        STATIC_IMPLICIT
    };  // Static propagated from above
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {"NONE", "VAUTOM", "VAUTOMI", "VSTATIC", "VSTATICI"};
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
    bool isAutomatic() const { return m_e == AUTOMATIC_EXPLICIT || m_e == AUTOMATIC_IMPLICIT; }
    bool isStatic() const { return m_e == STATIC_EXPLICIT || m_e == STATIC_IMPLICIT; }
    bool isStaticExplicit() const { return m_e == STATIC_EXPLICIT; }
    VLifetime makeImplicit() {
        switch (m_e) {
        case AUTOMATIC_EXPLICIT: return AUTOMATIC_IMPLICIT;
        case STATIC_EXPLICIT: return STATIC_IMPLICIT;
        default: return m_e;
        }
    }
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
    VNumRange(int hi, int lo, bool ascending) { init(hi, lo, ascending); }
    VNumRange(int left, int right)
        : m_left{left}
        , m_right{right}
        , m_ranged{true} {}
    ~VNumRange() = default;
    // MEMBERS
    void init(int hi, int lo, bool ascending) {
        if (lo > hi) {
            const int t = hi;
            hi = lo;
            lo = t;
        }
        m_left = ascending ? lo : hi;
        m_right = ascending ? hi : lo;
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
    int leftToRightInc() const { return ascending() ? 1 : -1; }
    int elements() const VL_MT_SAFE { return hi() - lo() + 1; }
    bool ranged() const { return m_ranged; }
    bool ascending() const { return m_left < m_right; }
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

// ######################################################################

class VPragmaType final {
public:
    enum en : uint8_t {
        COVERAGE_BLOCK_OFF,
        HIER_BLOCK,
        HIER_PARAMS,
        INLINE_MODULE,
        NO_INLINE_MODULE,
        NO_INLINE_TASK,
        PUBLIC_MODULE,
        PUBLIC_TASK,
        TIMEUNIT_SET,
        UNROLL_DISABLE,
        UNROLL_FULL,
        FULL_CASE,
        PARALLEL_CASE,
        _ENUM_SIZE
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {
            "COVERAGE_BLOCK_OFF",  //
            "HIER_BLOCK",  //
            "HIER_PARAMS",  //
            "INLINE_MODULE",  //
            "NO_INLINE_MODULE",  //
            "NO_INLINE_TASK",  //
            "PUBLIC_MODULE",  //
            "PUBLIC_TASK",  //
            "TIMEUNIT_SET",  //
            "UNROLL_DISABLE",  //
            "UNROLL_FULL",  //
            "FULL_CASE",  //
            "PARALLEL_CASE",  //
            "_ENUM_SIZE"  //
        };
        return names[m_e];
    }
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
inline std::ostream& operator<<(std::ostream& os, const VPragmaType& rhs) {
    return os << rhs.ascii();
}

// ######################################################################
// Defines what kind of randomization is done on a variable

class VRandAttr final {
public:
    enum en : uint8_t {
        NONE,  // Not randomizable
        RAND,  // Has a rand modifier
        RAND_CYCLIC,  // Has a randc modifier
        RAND_INLINE  // Not rand/randc, but used in inline random variable control
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {"NONE", "RAND", "RANDC", "RAND_INLINE"};
        return names[m_e];
    }
    VRandAttr()
        : m_e{NONE} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VRandAttr(en _e)
        : m_e{_e} {}
    constexpr operator en() const { return m_e; }
    bool isRandomizable() const { return m_e != NONE; }
    bool isRand() const { return m_e == RAND || m_e == RAND_CYCLIC; }
    bool isRandC() const { return m_e == RAND_CYCLIC; }
};
inline std::ostream& operator<<(std::ostream& os, const VRandAttr& rhs) {
    return os << rhs.ascii();
}

// ######################################################################
//  VSelfPointerText - Represents text to be emitted before a given var reference, call, etc. to
//  serve as a pointer to a 'self' object. For example, it could be empty (no self pointer), or the
//  string 'this', or 'vlSymsp->...'

class VSelfPointerText final {
    // STATIC MEMBERS
    // Keep these in shared pointers to avoid branching for special cases
    static const std::shared_ptr<const string> s_emptyp;  // Holds ""
    static const std::shared_ptr<const string> s_thisp;  // Holds "this"

    // MEMBERS
    std::shared_ptr<const string> m_strp;

public:
    // CONSTRUCTORS
    class Empty {};  // for creator type-overload selection
    explicit VSelfPointerText(Empty)
        : m_strp{s_emptyp} {}
    class This {};  // for creator type-overload selection
    explicit VSelfPointerText(This)
        : m_strp{s_thisp} {}
    VSelfPointerText(This, const string& field)
        : m_strp{std::make_shared<const string>("this->" + field)} {}
    class VlSyms {};  // for creator type-overload selection
    VSelfPointerText(VlSyms, const string& field)
        : m_strp{std::make_shared<const string>("(&vlSymsp->" + field + ')')} {}

    // METHODS
    bool isEmpty() const { return m_strp == s_emptyp; }
    bool isVlSym() const { return m_strp->find("vlSymsp") != string::npos; }
    bool hasThis() const { return m_strp == s_thisp || VString::startsWith(*m_strp, "this"); }
    string protect(bool useSelfForThis, bool protect) const;
    static string replaceThis(bool useSelfForThis, const string& text);
    const std::string& asString() const { return *m_strp; }
    bool operator==(const VSelfPointerText& other) const { return *m_strp == *other.m_strp; }
};

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

class VStrength final {
public:
    enum en : uint8_t { HIGHZ, SMALL, MEDIUM, WEAK, LARGE, PULL, STRONG, SUPPLY };
    enum en m_e;

    // cppcheck-suppress noExplicitConstructor
    constexpr VStrength(en strengthLevel)
        : m_e{strengthLevel} {}
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
//  VSystemCSectionType - Represents the type of a `systemc_* block (Verilator specific extension)

class VSystemCSectionType final {
public:
    enum en : uint8_t {
        CTOR,  // `systemc_ctor
        DTOR,  // `systemc_dtor
        HDR,  // `systemc_header
        HDR_POST,  // `systemc_header_post
        IMP,  // `systemc_implementation
        IMP_HDR,  // `systemc_imp_header
        INT  // `systemc_interface
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {"`systemc_ctor",  //
                                            "`systemc_dtor",  //
                                            "`systemc_header",  //
                                            "`systemc_header_post",  //
                                            "`systemc_implementation",  //
                                            "`systemc_imp_header",  //
                                            "`systemc_interface"};
        return names[m_e];
    }
    // cppcheck-suppress noExplicitConstructor
    constexpr VSystemCSectionType(en _e)
        : m_e{_e} {}
    constexpr operator en() const { return m_e; }
};

//######################################################################

class VTracePrefixType final {
public:
    enum en : uint8_t {
        // Note: Entries must match VerilatedTracePrefixType
        ARRAY_PACKED,
        ARRAY_UNPACKED,
        SCOPE_MODULE,
        SCOPE_INTERFACE,
        STRUCT_PACKED,
        STRUCT_UNPACKED,
        UNION_PACKED,
    };
    enum en m_e;
    // cppcheck-suppress noExplicitConstructor
    constexpr VTracePrefixType(en _e)
        : m_e{_e} {}
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[]
            = {"ARRAY_PACKED",  "ARRAY_UNPACKED",  "SCOPE_MODULE", "SCOPE_INTERFACE",
               "STRUCT_PACKED", "STRUCT_UNPACKED", "UNION_PACKED"};
        return names[m_e];
    }
};
constexpr bool operator==(const VTracePrefixType& lhs, const VTracePrefixType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VTracePrefixType& lhs, VTracePrefixType::en rhs) {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VTracePrefixType::en lhs, const VTracePrefixType& rhs) {
    return lhs == rhs.m_e;
}
inline std::ostream& operator<<(std::ostream& os, const VTracePrefixType& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class VTraceType final {
public:
    enum en : uint8_t {
        CONSTANT,  // Constant value dump (once at the beginning)
        FULL,  // Full value dump (always emitted)
        CHANGE  // Incremental value dump (emitted only if the value changed)
    };
    enum en m_e;
    VTraceType()
        : m_e{CONSTANT} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VTraceType(en _e)
        : m_e{_e} {}
    explicit VTraceType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"CONSTANT", "FULL", "CHANGE"};
        return names[m_e];
    }
};
constexpr bool operator==(const VTraceType& lhs, const VTraceType& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VTraceType& lhs, VTraceType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VTraceType::en lhs, const VTraceType& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VTraceType& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class VUseType final {
public:
    enum en : uint8_t {
        // Enum values are compared with <, so order matters
        INT_FWD_CLASS = 1 << 0,  // Interface (.h) needs a forward class declaration
        INT_INCLUDE = 1 << 1,  // Interface (.h) needs an include
    };
    enum en m_e;
    VUseType()
        : m_e{INT_FWD_CLASS} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VUseType(en _e)
        : m_e{_e} {}
    explicit VUseType(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    bool containsAny(VUseType other) { return m_e & other.m_e; }
    const char* ascii() const {
        static const char* const names[] = {"INT_FWD", "INT_INC", "INT_FWD_INC"};
        return names[m_e - 1];
    }
};
constexpr bool operator==(const VUseType& lhs, const VUseType& rhs) { return lhs.m_e == rhs.m_e; }
constexpr bool operator==(const VUseType& lhs, VUseType::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(VUseType::en lhs, const VUseType& rhs) { return lhs == rhs.m_e; }
constexpr VUseType::en operator|(VUseType::en lhs, VUseType::en rhs) {
    return VUseType::en((uint8_t)lhs | (uint8_t)rhs);
}
constexpr VUseType::en operator&(VUseType::en lhs, VUseType::en rhs) {
    return VUseType::en((uint8_t)lhs & (uint8_t)rhs);
}
inline std::ostream& operator<<(std::ostream& os, const VUseType& rhs) {
    return os << rhs.ascii();
}

// ######################################################################

class VVarType final {
public:
    enum en : uint8_t {
        UNKNOWN,
        GPARAM,
        LPARAM,
        SPECPARAM,
        GENVAR,
        VAR,  // Reg, integer, logic, etc
        SUPPLY0,
        SUPPLY1,
        WIRE,
        WREAL,
        TRIAND,
        TRIOR,
        TRIWIRE,
        TRI0,
        TRI1,
        PORT,  // Used in parser to recognize ports
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
        static const char* const names[]
            = {"?",        "GPARAM",  "LPARAM",   "SPECPARAM", "GENVAR",    "VAR",
               "SUPPLY0",  "SUPPLY1", "WIRE",     "WREAL",     "TRIAND",    "TRIOR",
               "TRIWIRE",  "TRI0",    "TRI1",     "PORT",      "BLOCKTEMP", "MODULETEMP",
               "STMTTEMP", "XTEMP",   "IFACEREF", "MEMBER"};
        return names[m_e];
    }
    bool isParam() const { return m_e == GPARAM || m_e == LPARAM; }
    bool isSignal() const {
        return (m_e == WIRE || m_e == WREAL || m_e == TRIWIRE || m_e == TRI0 || m_e == TRI1
                || m_e == PORT || m_e == SUPPLY0 || m_e == SUPPLY1 || m_e == VAR || m_e == TRIOR
                || m_e == TRIAND);
    }
    bool isNet() const {
        return (m_e == WIRE || m_e == TRIWIRE || m_e == TRI0 || m_e == TRI1 || m_e == SUPPLY0
                || m_e == SUPPLY1 || m_e == TRIOR || m_e == TRIAND);
    }
    bool isWor() const { return (m_e == TRIOR); }
    bool isWiredNet() const { return (m_e == TRIOR || m_e == TRIAND); }
    bool isContAssignable() const {  // In Verilog, always ok in SystemVerilog
        return (m_e == SUPPLY0 || m_e == SUPPLY1 || m_e == WIRE || m_e == WREAL || m_e == TRIWIRE
                || m_e == TRI0 || m_e == TRI1 || m_e == PORT || m_e == BLOCKTEMP
                || m_e == MODULETEMP || m_e == STMTTEMP || m_e == XTEMP || m_e == IFACEREF);
    }
    bool isProcAssignable() const {
        return (m_e == GPARAM || m_e == LPARAM || m_e == GENVAR || m_e == VAR || m_e == BLOCKTEMP
                || m_e == MODULETEMP || m_e == STMTTEMP || m_e == XTEMP || m_e == IFACEREF
                || m_e == MEMBER);
    }
    bool isTemp() const {
        return (m_e == BLOCKTEMP || m_e == MODULETEMP || m_e == STMTTEMP || m_e == XTEMP);
    }
    bool isVPIAccessible() const {
        return (m_e == VAR || m_e == GPARAM || m_e == LPARAM || m_e == SPECPARAM || m_e == PORT
                || m_e == WIRE || m_e == TRI0 || m_e == TRI1);
    }

    const char* traceSigKind() const {
        // VerilatedTraceSigKind to used in trace signal declaration
        static const char* const lut[] = {
            /* UNKNOWN:      */ "",  // Should not be traced
            /* GPARAM:       */ "PARAMETER",
            /* LPARAM:       */ "PARAMETER",
            /* SPECPARAM:    */ "PARAMETER",
            /* GENVAR:       */ "PARAMETER",
            /* VAR:          */ "VAR",
            /* SUPPLY0:      */ "SUPPLY0",
            /* SUPPLY1:      */ "SUPPLY1",
            /* WIRE:         */ "WIRE",
            /* WREAL:        */ "WIRE",
            /* TRIAND:       */ "TRIAND",
            /* TRIOR:        */ "TRIOR",
            /* TRIWIRE:      */ "TRI",
            /* TRI0:         */ "TRI0",
            /* TRI1:         */ "TRI1",
            /* PORT:         */ "WIRE",
            /* BLOCKTEMP:    */ "VAR",
            /* MODULETEMP:   */ "VAR",
            /* STMTTEMP:     */ "VAR",
            /* XTEMP:        */ "VAR",
            /* IFACEREF:     */ "",  // Should not be traced directly
            /* MEMBER:       */ "VAR",
        };
        return lut[m_e];
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

// Not in sorted order, as depends on above classes
class VBasicTypeKey final {
public:
    const int m_width;  // From AstNodeDType: Bit width of operation
    const int m_widthMin;  // From AstNodeDType: If unsized, bitwidth of minimum implementation
    const VNumRange m_nrange;  // From AstBasicDType: Numeric msb/lsb (if non-opaque keyword)
    const VSigning m_numeric;  // From AstNodeDType: Node is signed
    const VBasicDTypeKwd m_keyword;  // From AstBasicDType: What keyword created basic type
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
        , m_nrange{nrange}
        , m_numeric{numeric}
        , m_keyword{kwd} {}
    ~VBasicTypeKey() = default;
};

#endif  // Guard
