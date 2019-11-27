// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3AST_H_
#define _V3AST_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Number.h"
#include "V3Global.h"

#include <cmath>
#include VL_INCLUDE_UNORDERED_SET

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
typedef std::set<int> MTaskIdSet;  // Set of mtaskIds for Var sorting

//######################################################################

// For broken() function, return error string if have a match
#define BROKEN_RTN(test) do { if (VL_UNCOVERABLE(test)) return # test; } while(0)

// (V)erilator (N)ode is: True if AstNode is of a a given AstType
#define VN_IS(nodep,nodetypename) (AstNode::privateIs ## nodetypename(nodep))

// (V)erilator (N)ode cast: Cast to given type if can; effectively
// dynamic_cast<nodetypename>(nodep)
#define VN_CAST(nodep,nodetypename) (AstNode::privateCast ## nodetypename(nodep))
#define VN_CAST_CONST(nodep,nodetypename) (AstNode::privateConstCast ## nodetypename(nodep) )

// (V)erilator (N)ode deleted: Reference to deleted child (for assertions only)
#define VN_DELETED(nodep) VL_UNLIKELY((vluint64_t)(nodep) == 0x1)

//######################################################################

class AstType {
public:
#include "V3Ast__gen_types.h"  // From ./astgen
    // Above include has:
    //   enum en {...};
    //   const char* ascii() const {...};
    enum en m_e;
    // cppcheck-suppress uninitVar  // responsibility of each subclass
    inline AstType() {}
    // cppcheck-suppress noExplicitConstructor
    inline AstType(en _e) : m_e(_e) {}
    explicit inline AstType(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
  };
  inline bool operator==(AstType lhs, AstType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(AstType lhs, AstType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(AstType::en lhs, AstType rhs) { return (lhs == rhs.m_e); }
  inline std::ostream& operator<<(std::ostream& os, const AstType& rhs) { return os<<rhs.ascii(); }

//######################################################################

enum VSignedState {
    // This can't be in the fancy class as the lexer union will get upset
    signedst_UNSIGNED = 0, signedst_SIGNED = 1, signedst_NOSIGN = 2
};

//######################################################################

class AstNumeric {
public:
    enum en {
        UNSIGNED,
        SIGNED,
        NOSIGN,
        _ENUM_MAX  // Leave last
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {
            "UNSIGNED", "SIGNED", "NOSIGN"
        };
        return names[m_e];
    };
    inline AstNumeric() : m_e(UNSIGNED) {}
    // cppcheck-suppress noExplicitConstructor
    inline AstNumeric(en _e) : m_e(_e) {}
    // cppcheck-suppress noExplicitConstructor
    inline AstNumeric(VSignedState signst) {
        if (signst==signedst_UNSIGNED) m_e = UNSIGNED;
        else if (signst==signedst_SIGNED) m_e = SIGNED;
        else m_e = NOSIGN;
    }
    static inline AstNumeric fromBool(bool isSigned) {  // Factory method
        return isSigned ? AstNumeric(SIGNED) : AstNumeric(UNSIGNED); }
    explicit inline AstNumeric(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    inline bool isSigned() const { return m_e==SIGNED; }
    inline bool isNosign() const { return m_e==NOSIGN; }
    // No isUnsigned() as it's ambiguous if NOSIGN should be included or not.
  };
  inline bool operator==(AstNumeric lhs, AstNumeric rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(AstNumeric lhs, AstNumeric::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(AstNumeric::en lhs, AstNumeric rhs) { return (lhs == rhs.m_e); }
  inline std::ostream& operator<<(std::ostream& os, const AstNumeric& rhs) { return os<<rhs.ascii(); }

//######################################################################

class AstPragmaType {
public:
    enum en {
        ILLEGAL,
        COVERAGE_BLOCK_OFF,
        INLINE_MODULE,
        NO_INLINE_MODULE,
        NO_INLINE_TASK,
        PUBLIC_MODULE,
        PUBLIC_TASK
    };
    enum en m_e;
    inline AstPragmaType() : m_e(ILLEGAL) {}
    // cppcheck-suppress noExplicitConstructor
    inline AstPragmaType(en _e) : m_e(_e) {}
    explicit inline AstPragmaType(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
  };
  inline bool operator==(AstPragmaType lhs, AstPragmaType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(AstPragmaType lhs, AstPragmaType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(AstPragmaType::en lhs, AstPragmaType rhs) { return (lhs == rhs.m_e); }

//######################################################################

class AstCFuncType {
public:
    enum en {
        FT_NORMAL,
        TRACE_INIT,
        TRACE_INIT_SUB,
        TRACE_FULL,
        TRACE_FULL_SUB,
        TRACE_CHANGE,
        TRACE_CHANGE_SUB
    };
    enum en m_e;
    inline AstCFuncType() : m_e(FT_NORMAL) {}
    // cppcheck-suppress noExplicitConstructor
    inline AstCFuncType(en _e) : m_e(_e) {}
    explicit inline AstCFuncType(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    // METHODS
    bool isTrace() const { return (m_e==TRACE_INIT || m_e==TRACE_INIT_SUB
                                   || m_e==TRACE_FULL || m_e==TRACE_FULL_SUB
                                   || m_e==TRACE_CHANGE || m_e==TRACE_CHANGE_SUB); }
  };
  inline bool operator==(AstCFuncType lhs, AstCFuncType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(AstCFuncType lhs, AstCFuncType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(AstCFuncType::en lhs, AstCFuncType rhs) { return (lhs == rhs.m_e); }

//######################################################################

class VEdgeType {
public:
// REMEMBER to edit the strings below too
    enum en {
        // These must be in general -> most specific order, as we sort by it
        // in V3Const::visit AstSenTree
        ET_ILLEGAL,
        // Involving a variable
        ET_ANYEDGE,     // Default for sensitivities; rip them out
        ET_BOTHEDGE,    // POSEDGE | NEGEDGE
        ET_POSEDGE,
        ET_NEGEDGE,
        ET_HIGHEDGE,    // Is high now (latches)
        ET_LOWEDGE,     // Is low now (latches)
        // Not involving anything
        ET_COMBO,       // Sensitive to all combo inputs to this block
        ET_INITIAL,     // User initial statements
        ET_SETTLE,      // Like combo but for initial wire resolutions after initial statement
        ET_NEVER        // Never occurs (optimized away)
    };
    enum en m_e;
    bool clockedStmt() const {
        static const bool clocked[] = {
            false, false, true, true, true, true, true,
            false, false, false
        };
        return clocked[m_e];
    }
    VEdgeType invert() const {
        switch (m_e) {
        case ET_ANYEDGE:        return ET_ANYEDGE;
        case ET_BOTHEDGE:       return ET_BOTHEDGE;
        case ET_POSEDGE:        return ET_NEGEDGE;
        case ET_NEGEDGE:        return ET_POSEDGE;
        case ET_HIGHEDGE:       return ET_LOWEDGE;
        case ET_LOWEDGE:        return ET_HIGHEDGE;
        default: UASSERT_STATIC(0, "Inverting bad edgeType()");
        };
        return VEdgeType::ET_ILLEGAL;
    }
    const char* ascii() const {
        static const char* const names[] = {
            "%E-edge", "ANY", "BOTH", "POS", "NEG", "HIGH", "LOW",
            "COMBO", "INITIAL", "SETTLE", "NEVER"
        };
        return names[m_e];
    }
    const char* verilogKwd() const {
        static const char* const names[] = {
            "%E-edge", "[any]", "edge", "posedge", "negedge", "[high]", "[low]",
            "*", "[initial]", "[settle]", "[never]"
        };
        return names[m_e];
    }
    // Return true iff this and the other have mutually exclusive transitions
    bool exclusiveEdge(const VEdgeType& other) const {
        switch (m_e) {
        case VEdgeType::ET_POSEDGE:
            switch (other.m_e) {
            case VEdgeType::ET_NEGEDGE:  // FALLTHRU
            case VEdgeType::ET_LOWEDGE:
                return true;
            default: {}
            }
            break;
        case VEdgeType::ET_NEGEDGE:
            switch (other.m_e) {
            case VEdgeType::ET_POSEDGE:  // FALLTHRU
            case VEdgeType::ET_HIGHEDGE:
                return true;
            default: {}
            }
            break;
        default: {}
        }
        return false;
    }
    inline VEdgeType() : m_e(ET_ILLEGAL) {}
    // cppcheck-suppress noExplicitConstructor
    inline VEdgeType(en _e) : m_e(_e) {}
    explicit inline VEdgeType(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
  };
  inline bool operator==(VEdgeType lhs, VEdgeType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(VEdgeType lhs, VEdgeType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(VEdgeType::en lhs, VEdgeType rhs) { return (lhs == rhs.m_e); }

//######################################################################

class AstAttrType {
public:
    enum en {
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
        //
        MEMBER_BASE,                    // V3LinkResolve creates for AstPreSel, V3LinkParam removes
        //
        VAR_BASE,                       // V3LinkResolve creates for AstPreSel, V3LinkParam removes
        VAR_CLOCK,                      // V3LinkParse moves to AstVar::attrScClocked
        VAR_CLOCK_ENABLE,               // V3LinkParse moves to AstVar::attrClockEn
        VAR_PUBLIC,                     // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT,                // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT_RD,             // V3LinkParse moves to AstVar::sigPublic
        VAR_PUBLIC_FLAT_RW,             // V3LinkParse moves to AstVar::sigPublic
        VAR_ISOLATE_ASSIGNMENTS,        // V3LinkParse moves to AstVar::attrIsolateAssign
        VAR_SC_BV,                      // V3LinkParse moves to AstVar::attrScBv
        VAR_SFORMAT,                    // V3LinkParse moves to AstVar::attrSFormat
        VAR_CLOCKER,                    // V3LinkParse moves to AstVar::attrClocker
        VAR_NO_CLOCKER                  // V3LinkParse moves to AstVar::attrClocker
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {
            "%E-AT",
            "DIM_BITS", "DIM_DIMENSIONS", "DIM_HIGH", "DIM_INCREMENT", "DIM_LEFT",
            "DIM_LOW", "DIM_RIGHT", "DIM_SIZE", "DIM_UNPK_DIMENSIONS",
            "DT_PUBLIC",
            "ENUM_BASE", "ENUM_FIRST", "ENUM_LAST", "ENUM_NUM",
            "ENUM_NEXT", "ENUM_PREV", "ENUM_NAME",
            "MEMBER_BASE",
            "VAR_BASE", "VAR_CLOCK", "VAR_CLOCK_ENABLE", "VAR_PUBLIC",
            "VAR_PUBLIC_FLAT", "VAR_PUBLIC_FLAT_RD", "VAR_PUBLIC_FLAT_RW",
            "VAR_ISOLATE_ASSIGNMENTS", "VAR_SC_BV", "VAR_SFORMAT", "VAR_CLOCKER",
            "VAR_NO_CLOCKER"
        };
        return names[m_e];
    };
    inline AstAttrType() : m_e(ILLEGAL) {}
    // cppcheck-suppress noExplicitConstructor
    inline AstAttrType(en _e) : m_e(_e) {}
    explicit inline AstAttrType(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
  };
  inline bool operator==(AstAttrType lhs, AstAttrType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(AstAttrType lhs, AstAttrType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(AstAttrType::en lhs, AstAttrType rhs) { return (lhs == rhs.m_e); }

//######################################################################

class AstBasicDTypeKwd {
public:
    enum en {
        UNKNOWN,
        BIT, BYTE, CHANDLE, INT, INTEGER, LOGIC, LONGINT,
        DOUBLE, SHORTINT, FLOAT, TIME,
        // Closer to a class type, but limited usage
        STRING,
        // Internal types for mid-steps
        SCOPEPTR, CHARPTR,
        // Unsigned and two state; fundamental types
        UINT32, UINT64,
        // Internal types, eliminated after parsing
        LOGIC_IMPLICIT,
        // Leave last
        _ENUM_MAX
    };
    enum en m_e;
    const char* ascii() const {
        static const char* const names[] = {
            "%E-unk",
            "bit", "byte", "chandle", "int", "integer", "logic", "longint",
            "real", "shortint", "shortreal", "time",
            "string",
            "VerilatedScope*", "char*",
            "IData", "QData",
            "LOGIC_IMPLICIT",
            " MAX"
        };
        return names[m_e];
    };
    const char* dpiType() const {
        static const char* const names[] = {
            "%E-unk",
            "unsigned char", "char", "void*", "int", "int", "svLogic", "long long",
            "double", "short int", "float", "long long",
            "const char*",
            "dpiScope", "const char*",
            "IData", "QData",
            "svLogic",  // Though shouldn't be needed
            " MAX"
        };
        return names[m_e];
    };
    static void selfTest() {
        UASSERT(0==strcmp(AstBasicDTypeKwd(_ENUM_MAX).ascii(), " MAX"), "SelfTest: Enum mismatch");
        UASSERT(0==strcmp(AstBasicDTypeKwd(_ENUM_MAX).dpiType(), " MAX"), "SelfTest: Enum mismatch");
    }
    inline AstBasicDTypeKwd() : m_e(UNKNOWN) {}
    // cppcheck-suppress noExplicitConstructor
    inline AstBasicDTypeKwd(en _e) : m_e(_e) {}
    explicit inline AstBasicDTypeKwd(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    int width() const {
        switch (m_e) {
        case BIT:       return 1;   // scalar, can't bit extract unless ranged
        case BYTE:      return 8;
        case CHANDLE:   return 64;
        case INT:       return 32;
        case INTEGER:   return 32;
        case LOGIC:     return 1;   // scalar, can't bit extract unless ranged
        case LONGINT:   return 64;
        case DOUBLE:    return 64;  // opaque
        case FLOAT:     return 32;  // opaque
        case SHORTINT:  return 16;
        case TIME:      return 64;
        case STRING:    return 64;  // opaque  // Just the pointer, for today
        case SCOPEPTR:  return 0;   // opaque
        case CHARPTR:   return 0;   // opaque
        case UINT32:    return 32;
        case UINT64:    return 64;
        default: return 0;
        }
    }
    bool isSigned() const {
        return m_e==BYTE || m_e==SHORTINT || m_e==INT || m_e==LONGINT || m_e==INTEGER
            || m_e==DOUBLE || m_e==FLOAT;
    }
    bool isUnsigned() const {
        return m_e==CHANDLE || m_e==STRING || m_e==SCOPEPTR || m_e==CHARPTR
            || m_e==UINT32 || m_e==UINT64;
    }
    bool isFourstate() const {
        return m_e==INTEGER || m_e==LOGIC || m_e==LOGIC_IMPLICIT;
    }
    bool isZeroInit() const {  // Otherwise initializes to X
        return (m_e==BIT || m_e==BYTE || m_e==CHANDLE || m_e==INT || m_e==LONGINT || m_e==SHORTINT
                || m_e==STRING || m_e==DOUBLE || m_e==FLOAT);
    }
    bool isIntNumeric() const {  // Enum increment supported
        return (m_e==BIT || m_e==BYTE || m_e==INT || m_e==INTEGER || m_e==LOGIC
                || m_e==LONGINT || m_e==SHORTINT || m_e==UINT32 || m_e==UINT64);
    }
    bool isSloppy() const {  // Don't be as anal about width warnings
        return !(m_e==LOGIC || m_e==BIT);
    }
    bool isBitLogic() const {  // Bit/logic vector types; can form a packed array
        return (m_e==LOGIC || m_e==BIT);
    }
    bool isDpiBitVal() const {  // DPI uses svBitVecVal
        return m_e==BIT;
    }
    bool isDpiLogicVal() const {  // DPI uses svLogicVecVal
        return m_e==INTEGER || m_e==LOGIC || m_e==LOGIC_IMPLICIT || m_e==TIME;
    }
    bool isDpiUnreturnable() const {  // Not legal as DPI function return
        return isDpiLogicVal();
    }
    bool isDpiUnsignable() const {  // Can add "unsigned" to DPI
        return (m_e==BYTE || m_e==SHORTINT || m_e==INT || m_e==LONGINT || m_e==INTEGER);
    }
    bool isDpiCLayout() const {  // Uses standard C layout, for DPI runtime access
        return (m_e==BIT || m_e==BYTE || m_e==CHANDLE || m_e==INT
                || m_e==LONGINT || m_e==DOUBLE || m_e==SHORTINT || m_e==UINT32 || m_e==UINT64);
    }
    bool isOpaque() const {  // IE not a simple number we can bit optimize
        return (m_e==STRING || m_e==SCOPEPTR || m_e==CHARPTR || m_e==DOUBLE || m_e==FLOAT);
    }
    bool isDouble() const { return m_e==DOUBLE; }
    bool isString() const { return m_e==STRING; }
  };
  inline bool operator==(AstBasicDTypeKwd lhs, AstBasicDTypeKwd rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(AstBasicDTypeKwd lhs, AstBasicDTypeKwd::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(AstBasicDTypeKwd::en lhs, AstBasicDTypeKwd rhs) { return (lhs == rhs.m_e); }

//######################################################################

class VDirection {
public:
    enum en {
        NONE,
        INPUT,
        OUTPUT,
        INOUT,
        REF,
        CONSTREF
    };
    enum en m_e;
    inline VDirection() : m_e(NONE) {}
    // cppcheck-suppress noExplicitConstructor
    inline VDirection(en _e) : m_e(_e) {}
    explicit inline VDirection(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {
            "NONE", "INPUT", "OUTPUT", "INOUT", "REF", "CONSTREF"};
        return names[m_e]; }
    string verilogKwd() const {
        static const char* const names[] = {
            "", "input", "output", "inout", "ref", "const ref"};
        return names[m_e]; }
    string xmlKwd() const {  // For historical reasons no "put" suffix
        static const char* const names[] = {
            "", "in", "out", "inout", "ref", "const ref"};
        return names[m_e]; }
    string prettyName() const { return verilogKwd(); }
    bool isAny() const { return m_e != NONE; }
    // Looks like inout - "ish" because not identical to being an INOUT
    bool isInoutish() const { return m_e == INOUT; }
    bool isNonOutput() const { return m_e == INPUT || m_e == INOUT
            || m_e == REF || m_e == CONSTREF; }
    bool isReadOnly() const { return m_e == INPUT || m_e == CONSTREF; }
    bool isWritable() const { return m_e == OUTPUT || m_e == INOUT
            || m_e == REF; }
    bool isRefOrConstRef() const { return m_e == REF || m_e == CONSTREF; }
  };
  inline bool operator==(VDirection lhs, VDirection rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(VDirection lhs, VDirection::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(VDirection::en lhs, VDirection rhs) { return (lhs == rhs.m_e); }
  inline std::ostream& operator<<(std::ostream& os, const VDirection& rhs) { return os<<rhs.ascii(); }

//######################################################################

/// Boolean or unknown
class VBoolOrUnknown {
public:
    enum en {
        BU_FALSE=0,
        BU_TRUE=1,
        BU_UNKNOWN=2,
        _ENUM_END
    };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    inline VBoolOrUnknown() : m_e(BU_UNKNOWN) {}
    // cppcheck-suppress noExplicitConstructor
    inline VBoolOrUnknown(en _e) : m_e(_e) {}
    explicit inline VBoolOrUnknown(int _e) : m_e(static_cast<en>(_e)) {}
    const char* ascii() const {
        static const char* const names[] = {
            "FALSE", "TRUE", "UNK"};
        return names[m_e]; }
    bool trueU() const { return m_e == BU_TRUE || m_e == BU_UNKNOWN; }
    bool falseU() const { return m_e == BU_FALSE || m_e == BU_UNKNOWN; }
    bool unknown() const { return m_e == BU_UNKNOWN; }
  };
  inline bool operator==(VBoolOrUnknown lhs, VBoolOrUnknown rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(VBoolOrUnknown lhs, VBoolOrUnknown::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(VBoolOrUnknown::en lhs, VBoolOrUnknown rhs) { return (lhs == rhs.m_e); }
  inline std::ostream& operator<<(std::ostream& os, const VBoolOrUnknown& rhs) { return os<<rhs.ascii(); }

//######################################################################

class AstVarType {
public:
    enum en {
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
        PORT,           // Temp type used in parser only
        BLOCKTEMP,
        MODULETEMP,
        STMTTEMP,
        XTEMP,
        IFACEREF        // Used to link Interfaces between modules
    };
    enum en m_e;
    inline AstVarType() : m_e(UNKNOWN) {}
    // cppcheck-suppress noExplicitConstructor
    inline AstVarType(en _e) : m_e(_e) {}
    explicit inline AstVarType(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {
            "?", "GPARAM", "LPARAM", "GENVAR", "VAR",
            "SUPPLY0", "SUPPLY1", "WIRE", "WREAL", "IMPLICITWIRE",
            "TRIWIRE", "TRI0", "TRI1",
            "PORT",
            "BLOCKTEMP", "MODULETEMP", "STMTTEMP", "XTEMP",
            "IFACEREF"};
        return names[m_e]; }
    bool isSignal() const {
        return (m_e==WIRE || m_e==WREAL || m_e==IMPLICITWIRE
                || m_e==TRIWIRE
                || m_e==TRI0 || m_e==TRI1 || m_e==PORT
                || m_e==SUPPLY0 || m_e==SUPPLY1
                || m_e==VAR);
    }
    bool isContAssignable() const {  // In Verilog, always ok in SystemVerilog
        return (m_e==SUPPLY0 || m_e==SUPPLY1
                || m_e==WIRE || m_e==WREAL || m_e==IMPLICITWIRE
                || m_e==TRIWIRE || m_e==TRI0 || m_e==TRI1 || m_e==PORT
                || m_e==BLOCKTEMP || m_e==MODULETEMP || m_e==STMTTEMP
                || m_e==XTEMP || m_e==IFACEREF);
    }
    bool isProcAssignable() const {
        return (m_e==GPARAM || m_e==LPARAM || m_e==GENVAR
                || m_e==VAR
                || m_e==BLOCKTEMP || m_e==MODULETEMP || m_e==STMTTEMP
                || m_e==XTEMP || m_e==IFACEREF);
    }
    bool isTemp() const {
        return (m_e==BLOCKTEMP || m_e==MODULETEMP || m_e==STMTTEMP || m_e==XTEMP);
    }
  };
  inline bool operator==(AstVarType lhs, AstVarType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(AstVarType lhs, AstVarType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(AstVarType::en lhs, AstVarType rhs) { return (lhs == rhs.m_e); }
  inline std::ostream& operator<<(std::ostream& os, const AstVarType& rhs) { return os<<rhs.ascii(); }

//######################################################################

class VBranchPred {
public:
    enum en {
        BP_UNKNOWN=0,
        BP_LIKELY,
        BP_UNLIKELY,
        _ENUM_END
    };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    inline VBranchPred() : m_e(BP_UNKNOWN) {}
    // cppcheck-suppress noExplicitConstructor
    inline VBranchPred(en _e) : m_e(_e) {}
    explicit inline VBranchPred(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    bool unknown() const { return m_e == BP_UNKNOWN; }
    bool likely() const { return m_e == BP_LIKELY; }
    bool unlikely() const { return m_e == BP_UNLIKELY; }
    VBranchPred invert() const {
        if (m_e==BP_UNLIKELY) return BP_LIKELY;
        else if (m_e==BP_LIKELY) return BP_UNLIKELY;
        else return m_e;
    }
    const char* ascii() const {
        static const char* const names[] = {
            "", "VL_LIKELY", "VL_UNLIKELY"};
        return names[m_e]; }
  };
  inline bool operator==(VBranchPred lhs, VBranchPred rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(VBranchPred lhs, VBranchPred::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(VBranchPred::en lhs, VBranchPred rhs) { return (lhs == rhs.m_e); }
  inline std::ostream& operator<<(std::ostream& os, const VBranchPred& rhs) { return os<<rhs.ascii(); }

//######################################################################

class VVarAttrClocker {
public:
    enum en {
        CLOCKER_UNKNOWN=0,
        CLOCKER_YES,
        CLOCKER_NO,
        _ENUM_END
    };
    enum en m_e;
    // CONSTRUCTOR - note defaults to *UNKNOWN*
    inline VVarAttrClocker() : m_e(CLOCKER_UNKNOWN) {}
    // cppcheck-suppress noExplicitConstructor
    inline VVarAttrClocker(en _e) : m_e(_e) {}
    explicit inline VVarAttrClocker(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    bool unknown() const { return m_e==CLOCKER_UNKNOWN; }
    VVarAttrClocker invert() const {
        if (m_e==CLOCKER_YES) return CLOCKER_NO;
        else if (m_e==CLOCKER_NO) return CLOCKER_YES;
        else return m_e;
    }
    const char* ascii() const {
        static const char* const names[] = {
            "", "clker", "non_clker"};
        return names[m_e]; }
  };
  inline bool operator==(VVarAttrClocker lhs, VVarAttrClocker rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(VVarAttrClocker lhs, VVarAttrClocker::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(VVarAttrClocker::en lhs, VVarAttrClocker rhs) { return (lhs == rhs.m_e); }
  inline std::ostream& operator<<(std::ostream& os, const VVarAttrClocker& rhs) { return os<<rhs.ascii(); }

//######################################################################

class VAlwaysKwd {
public:
    enum en {
        ALWAYS,
        ALWAYS_FF,
        ALWAYS_LATCH,
        ALWAYS_COMB
    };
    enum en m_e;
    inline VAlwaysKwd() : m_e(ALWAYS) {}
    // cppcheck-suppress noExplicitConstructor
    inline VAlwaysKwd(en _e) : m_e(_e) {}
    explicit inline VAlwaysKwd(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {
            "always", "always_ff", "always_latch", "always_comb"};
        return names[m_e]; }
  };
  inline bool operator==(VAlwaysKwd lhs, VAlwaysKwd rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(VAlwaysKwd lhs, VAlwaysKwd::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(VAlwaysKwd::en lhs, VAlwaysKwd rhs) { return (lhs == rhs.m_e); }

//######################################################################

class VCaseType {
public:
    enum en {
        CT_CASE,
        CT_CASEX,
        CT_CASEZ,
        CT_CASEINSIDE
    };
    enum en m_e;
    inline VCaseType() : m_e(CT_CASE) {}
    // cppcheck-suppress noExplicitConstructor
    inline VCaseType(en _e) : m_e(_e) {}
    explicit inline VCaseType(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
  };
  inline bool operator==(VCaseType lhs, VCaseType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(VCaseType lhs, VCaseType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(VCaseType::en lhs, VCaseType rhs) { return (lhs == rhs.m_e); }

//######################################################################

class AstDisplayType {
public:
    enum en {
        DT_DISPLAY,
        DT_WRITE,
        DT_INFO,
        DT_ERROR,
        DT_WARNING,
        DT_FATAL
    };
    enum en m_e;
    inline AstDisplayType() : m_e(DT_DISPLAY) {}
    // cppcheck-suppress noExplicitConstructor
    inline AstDisplayType(en _e) : m_e(_e) {}
    explicit inline AstDisplayType(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    bool addNewline() const { return m_e!=DT_WRITE; }
    bool needScopeTracking() const { return m_e!=DT_DISPLAY && m_e!=DT_WRITE; }
    const char* ascii() const {
        static const char* const names[] = {
            "display", "write", "info", "error", "warning", "fatal"};
        return names[m_e]; }
  };
  inline bool operator==(AstDisplayType lhs, AstDisplayType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(AstDisplayType lhs, AstDisplayType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(AstDisplayType::en lhs, AstDisplayType rhs) { return (lhs == rhs.m_e); }

//######################################################################

class VParseRefExp {
public:
    enum en {
        PX_NONE,        // Used in V3LinkParse only
        PX_TEXT         // Unknown ID component
    };
    enum en m_e;
    inline VParseRefExp() : m_e(PX_NONE) {}
    // cppcheck-suppress noExplicitConstructor
    inline VParseRefExp(en _e) : m_e(_e) {}
    explicit inline VParseRefExp(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {
            "", "TEXT", "PREDOT"};
        return names[m_e]; }
  };
  inline bool operator==(VParseRefExp lhs, VParseRefExp rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator==(VParseRefExp lhs, VParseRefExp::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator==(VParseRefExp::en lhs, VParseRefExp rhs) { return (lhs == rhs.m_e); }
  inline std::ostream& operator<<(std::ostream& os, const VParseRefExp& rhs) { return os<<rhs.ascii(); }

//######################################################################
// VNumRange - Structure containing numeric range information
// See also AstRange, which is a symbolic version of this

class VNumRange {
public:
    int m_hi;  // HI part, HI always >= LO
    int m_lo;  // LO
    union {
        int mu_flags;
        struct {
            bool m_ranged:1;  // Has a range
            bool m_littleEndian:1;  // Bit vector is little endian
        };
    };
    inline bool operator==(const VNumRange& rhs) const {
        return m_hi == rhs.m_hi
            && m_lo == rhs.m_lo
            && mu_flags == rhs.mu_flags; }
    inline bool operator< (const VNumRange& rhs) const {
        if ( (m_hi <  rhs.m_hi)) return true;
        if (!(m_hi == rhs.m_hi)) return false;  // lhs > rhs
        if ( (m_lo <  rhs.m_lo)) return true;
        if (!(m_lo == rhs.m_lo)) return false;  // lhs > rhs
        if ( (mu_flags <  rhs.mu_flags)) return true;
        if (!(mu_flags == rhs.mu_flags)) return false;  // lhs > rhs
        return false;
    }
    //
    class LeftRight {};
    VNumRange() : m_hi(0), m_lo(0), mu_flags(0) {}
    VNumRange(int hi, int lo, bool littleEndian)
        : m_hi(0), m_lo(0), mu_flags(0)
        { init(hi, lo, littleEndian); }
    VNumRange(LeftRight, int left, int right)
        : m_hi(0), m_lo(0), mu_flags(0)
        { init((right>left)?right:left, (right>left)?left:right, (right>left)); }
    ~VNumRange() {}
    // MEMBERS
    void init(int hi, int lo, bool littleEndian) {
        m_hi = hi; m_lo = lo; mu_flags = 0; m_ranged = true; m_littleEndian = littleEndian;
    }
    int hi() const { return m_hi; }
    int lo() const { return m_lo; }
    int left() const { return littleEndian()?lo():hi(); }  // How to show a declaration
    int right() const { return littleEndian()?hi():lo(); }
    int leftToRightInc() const { return littleEndian()?1:-1; }
    int elements() const { return hi()-lo()+1; }
    bool ranged() const { return m_ranged; }
    bool littleEndian() const { return m_littleEndian; }
    int hiMaxSelect() const { return (lo()<0 ? hi()-lo() : hi()); }  // Maximum value a [] select may index
    bool representableByWidth() const {  // Could be represented by just width=1, or [width-1:0]
        return (!m_ranged || (m_lo==0 && m_hi>=1 && !m_littleEndian)); }
    void dump(std::ostream& str) const {
        if (ranged()) str<<"["<<left()<<":"<<right()<<"]"; else str<<"[norg]"; }
};
inline std::ostream& operator<<(std::ostream& os, const VNumRange& rhs) { rhs.dump(os); return os; }

//######################################################################

class VBasicTypeKey {
public:
    int         m_width;        // From AstNodeDType: Bit width of operation
    int         m_widthMin;     // From AstNodeDType: If unsized, bitwidth of minimum implementation
    AstNumeric  m_numeric;      // From AstNodeDType: Node is signed
    AstBasicDTypeKwd m_keyword;  // From AstBasicDType: What keyword created basic type
    VNumRange   m_nrange;       // From AstBasicDType: Numeric msb/lsb (if non-opaque keyword)
    inline bool operator==(const VBasicTypeKey& rhs) const {
        return m_width == rhs.m_width
            && m_widthMin == rhs.m_widthMin
            && m_numeric == rhs.m_numeric
            && m_keyword == rhs.m_keyword
            && m_nrange == rhs.m_nrange; }
    inline bool operator< (const VBasicTypeKey& rhs) const {
        if ( (m_width <  rhs.m_width)) return true;
        if (!(m_width == rhs.m_width)) return false;  // lhs > rhs
        if ( (m_widthMin <  rhs.m_widthMin)) return true;
        if (!(m_widthMin == rhs.m_widthMin)) return false;  // lhs > rhs
        if ( (m_numeric <  rhs.m_numeric)) return true;
        if (!(m_numeric == rhs.m_numeric)) return false;  // lhs > rhs
        if ( (m_keyword <  rhs.m_keyword)) return true;
        if (!(m_keyword == rhs.m_keyword)) return false;  // lhs > rhs
        if ( (m_nrange <  rhs.m_nrange)) return true;
        if (!(m_nrange == rhs.m_nrange)) return false;  // lhs > rhs
        return false; }
    VBasicTypeKey(int width, int widthMin, AstNumeric numeric, AstBasicDTypeKwd kwd,
                  const VNumRange& nrange)
        : m_width(width), m_widthMin(widthMin), m_numeric(numeric),
          m_keyword(kwd), m_nrange(nrange) {}
    ~VBasicTypeKey() {}
};

//######################################################################
// AstNUser - Generic base class for AST User nodes.
//          - Also used to allow parameter passing up/down iterate calls

class WidthVP;
class LinkVP;
class OrderBlockNU;
class OrderVarNU;
class V3GraphVertex;
class VSymEnt;

class VNUser {
    union {
        void* up;
        int ui;
    } m_u;
public:
    VNUser() {}
    // non-explicit:
    // cppcheck-suppress noExplicitConstructor
    VNUser(int i) { m_u.up = 0; m_u.ui = i; }
    explicit VNUser(void* p) { m_u.up = p; }
    ~VNUser() {}
    // Casters
    WidthVP* c() { return ((WidthVP*)m_u.up); }
    LinkVP* toLinkVP() { return ((LinkVP*)m_u.up); }
    VSymEnt* toSymEnt() { return ((VSymEnt*)m_u.up); }
    AstNode* toNodep() { return ((AstNode*)m_u.up); }
    OrderBlockNU* toOrderBlock() { return ((OrderBlockNU*)m_u.up); }
    OrderVarNU* toOrderVar() { return ((OrderVarNU*)m_u.up); }
    V3GraphVertex* toGraphVertex() { return ((V3GraphVertex*)m_u.up); }
    inline int  toInt() {
        return m_u.ui;
    }
    static inline VNUser fromZero() { return VNUser(0); }
    static inline VNUser fromInt(int i) { return VNUser(i); }
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

class AstUserInUseBase {
protected:
    static void allocate(int id, uint32_t& cntGblRef, bool& userBusyRef) {
        // Perhaps there's still a AstUserInUse in scope for this?
        UASSERT_STATIC(!userBusyRef, "Conflicting user use; AstUser"+cvtToStr(id)+"InUse request when under another AstUserInUse");
        userBusyRef = true;
        clearcnt(id, cntGblRef, userBusyRef);
    }
    static void free(int id, uint32_t& cntGblRef, bool& userBusyRef) {
        UASSERT_STATIC(userBusyRef, "Free of User"+cvtToStr(id)+"() not under AstUserInUse");
        clearcnt(id, cntGblRef, userBusyRef);  // Includes a checkUse for us
        userBusyRef = false;
    }
    static void clearcnt(int id, uint32_t& cntGblRef, bool& userBusyRef) {
        UASSERT_STATIC(userBusyRef, "Clear of User"+cvtToStr(id)+"() not under AstUserInUse");
        // If this really fires and is real (after 2^32 edits???)
        // we could just walk the tree and clear manually
        ++cntGblRef;
        UASSERT_STATIC(cntGblRef, "User*() overflowed!");
    }
    static void checkcnt(int id, uint32_t&, bool& userBusyRef) {
        UASSERT_STATIC(userBusyRef, "Check of User"+cvtToStr(id)+"() failed, not under AstUserInUse");
    }
};

// For each user() declare the in use structure
// We let AstNode peek into here, because when under low optimization even
// an accessor would be way too slow.
class AstUser1InUse : AstUserInUseBase {
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
class AstUser2InUse : AstUserInUseBase {
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
class AstUser3InUse : AstUserInUseBase {
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
class AstUser4InUse : AstUserInUseBase {
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
class AstUser5InUse : AstUserInUseBase {
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

//######################################################################
// AstNVisitor -- Allows new functions to be called on each node
// type without changing the base classes.  See "Modern C++ Design".

class AstNVisitor {
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
        m_deleteps.push_back(nodep);
    }
    /// Call deleteTree on all previously pushDeletep()'ed nodes
    void doDeletes();
public:
    virtual ~AstNVisitor() {
        doDeletes();
    }
    /// Call visit()s on nodep
    void iterate(AstNode* nodep);
    /// Call visit()s on nodep's children
    void iterateChildren(AstNode* nodep);
    /// Call visit()s on nodep's children in backp() order
    void iterateChildrenBackwards(AstNode* nodep);
    /// Call visit()s on const nodep's children
    void iterateChildrenConst(AstNode* nodep);
    /// Call visit()s on nodep (maybe NULL) and nodep's nextp() list
    void iterateAndNextNull(AstNode* nodep);
    /// Call visit()s on const nodep (maybe NULL) and nodep's nextp() list
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

class AstNRelinker {
protected:
    friend class AstNode;
    enum RelinkWhatEn {
        RELINK_BAD, RELINK_NEXT, RELINK_OP1, RELINK_OP2, RELINK_OP3, RELINK_OP4
    };
    AstNode* m_oldp;  // The old node that was linked to this point in the tree
    AstNode* m_backp;
    RelinkWhatEn m_chg;
    AstNode** m_iterpp;
public:
    AstNRelinker() { m_oldp = NULL; m_backp = NULL; m_chg = RELINK_BAD; m_iterpp = NULL; }
    void relink(AstNode* newp);
    AstNode* oldp() const { return m_oldp; }
    void dump(std::ostream& str=std::cout) const;
};
inline std::ostream& operator<<(std::ostream& os, const AstNRelinker& rhs) {
    rhs.dump(os); return os; }

//######################################################################
// V3Hash -- Node hashing for V3Combine

class V3Hash {
    // A hash of a tree of nodes, consisting of 8 bits with the number of nodes in the hash
    // and 24 bit value hash of relevant information about the node.
    // A value of 0 is illegal
    uint32_t    m_both;
    static const uint32_t M24 = ((1<<24)-1);
    void setBoth(uint32_t depth, uint32_t hshval) {
        if (depth==0) depth = 1;
        if (depth>255) depth = 255;
        m_both = (depth<<24) | (hshval & M24);
    }
public:
    // METHODS
    bool isIllegal() const { return m_both==0; }
    uint32_t fullValue() const { return m_both; }
    uint32_t depth() const { return (m_both >> 24) & 255; }
    uint32_t hshval() const { return m_both & M24; }
    // OPERATORS
    inline bool operator==(const V3Hash& rh) const { return m_both==rh.m_both; }
    inline bool operator!=(const V3Hash& rh) const { return m_both!=rh.m_both; }
    inline bool operator<(const V3Hash& rh) const { return m_both<rh.m_both; }
    // CONSTRUCTORS
    class Illegal {};  // for creator type-overload selection
    class FullValue {};  // for creator type-overload selection
    explicit V3Hash(Illegal) { m_both = 0; }
    // Saving and restoring inside a userp
    explicit V3Hash(VNUser u) { m_both = u.toInt(); }
    V3Hash operator+= (const V3Hash& rh) {
        setBoth(depth()+rh.depth(), (hshval()*31+rh.hshval()));
        return *this; };
    // Creating from raw data (sameHash functions)
    V3Hash() { setBoth(1, 0); }
    // cppcheck-suppress noExplicitConstructor
    V3Hash(uint32_t val) { setBoth(1, val); }
    // cppcheck-suppress noExplicitConstructor
    V3Hash(const void* vp) { setBoth(1, cvtToHash(vp)); }
    // cppcheck-suppress noExplicitConstructor
    V3Hash(const string& name);
    V3Hash(V3Hash h1, V3Hash h2) {
        setBoth(1, h1.hshval()*31+h2.hshval()); }
    V3Hash(V3Hash h1, V3Hash h2, V3Hash h3) {
        setBoth(1, (h1.hshval()*31+h2.hshval())*31+h3.hshval()); }
    V3Hash(V3Hash h1, V3Hash h2, V3Hash h3, V3Hash h4) {
        setBoth(1, ((h1.hshval()*31+h2.hshval())*31+h3.hshval())*31+h4.hshval()); }
};
std::ostream& operator<<(std::ostream& os, const V3Hash& rhs);

//######################################################################
// Callback base class to determine if node matches some formula

class VNodeMatcher {
public:
    virtual bool nodeMatch(const AstNode* nodep) const { return true; }
};

//######################################################################
// AstNode -- Base type of all Ast types

// Prefetch a node.
// The if() makes it faster, even though prefetch won't fault on null pointers
#define ASTNODE_PREFETCH(nodep) \
    { if (nodep) { VL_PREFETCH_RD(&((nodep)->m_nextp)); VL_PREFETCH_RD(&((nodep)->m_iterpp)); }}

class AstNode {
    // v ASTNODE_PREFETCH depends on below ordering of members
    AstNode*    m_nextp;        // Next peer in the parent's list
    AstNode*    m_backp;        // Node that points to this one (via next/op1/op2/...)
    AstNode*    m_op1p;         // Generic pointer 1
    AstNode*    m_op2p;         // Generic pointer 2
    AstNode*    m_op3p;         // Generic pointer 3
    AstNode*    m_op4p;         // Generic pointer 4
    AstNode**   m_iterpp;       // Pointer to node iterating on, change it if we replace this node.
    // ^ ASTNODE_PREFETCH depends on above ordering of members

    AstNode*    m_headtailp;    // When at begin/end of list, the opposite end of the list

    FileLine*   m_fileline;     // Where it was declared
    vluint64_t  m_editCount;    // When it was last edited
    static vluint64_t s_editCntGbl;  // Global edit counter
    static vluint64_t s_editCntLast;  // Global edit counter, last value for printing * near node #s

    AstNodeDType* m_dtypep;     // Data type of output or assignment (etc)

    AstNode*    m_clonep;       // Pointer to clone of/ source of this module (for *LAST* cloneTree() ONLY)
    int         m_cloneCnt;     // Mark of when userp was set
    static int  s_cloneCntGbl;  // Count of which userp is set

    // Attributes
    bool        m_didWidth:1;   // Did V3Width computation
    bool        m_doingWidth:1;  // Inside V3Width
    bool        m_protect:1;    // Protect name if protection is on
    //          // Space for more bools here

    // This member ordering both allows 64 bit alignment and puts associated data together
    VNUser      m_user1u;       // Contains any information the user iteration routine wants
    uint32_t    m_user1Cnt;     // Mark of when userp was set
    uint32_t    m_user2Cnt;     // Mark of when userp was set
    VNUser      m_user2u;       // Contains any information the user iteration routine wants
    VNUser      m_user3u;       // Contains any information the user iteration routine wants
    uint32_t    m_user3Cnt;     // Mark of when userp was set
    uint32_t    m_user4Cnt;     // Mark of when userp was set
    VNUser      m_user4u;       // Contains any information the user iteration routine wants
    VNUser      m_user5u;       // Contains any information the user iteration routine wants
    uint32_t    m_user5Cnt;     // Mark of when userp was set

    // METHODS
    void        op1p(AstNode* nodep) { m_op1p = nodep; if (nodep) nodep->m_backp = this; }
    void        op2p(AstNode* nodep) { m_op2p = nodep; if (nodep) nodep->m_backp = this; }
    void        op3p(AstNode* nodep) { m_op3p = nodep; if (nodep) nodep->m_backp = this; }
    void        op4p(AstNode* nodep) { m_op4p = nodep; if (nodep) nodep->m_backp = this; }

    void        init();  // initialize value of AstNode
private:
    AstNode*    cloneTreeIter();
    AstNode*    cloneTreeIterList();
    void        checkTreeIter(AstNode* backp);
    void        checkTreeIterList(AstNode* backp);
    bool        gateTreeIter() const;
    static bool sameTreeIter(const AstNode* node1p, const AstNode* node2p,
                             bool ignNext, bool gateOnly);
    void        deleteTreeIter();
    void        deleteNode();
    string      locationStr() const;
public:
    static void relinkOneLink(AstNode*& pointpr, AstNode* newp);
    // cppcheck-suppress functionConst
    void        debugTreeChange(const char* prefix, int lineno, bool next);

protected:
    // CONSTRUCTORS
    AstNode() { init(); }
    explicit AstNode(FileLine* fileline) {init(); m_fileline = fileline; }
    virtual AstNode* clone() = 0;  // Generally, cloneTree is what you want instead
    virtual void cloneRelink() {}
    void cloneRelinkTree();

    // METHODS
    void setOp1p(AstNode* newp);  // Set non-list-type op1 to non-list element
    void setOp2p(AstNode* newp);  // Set non-list-type op2 to non-list element
    void setOp3p(AstNode* newp);  // Set non-list-type op3 to non-list element
    void setOp4p(AstNode* newp);  // Set non-list-type op4 to non-list element

    void setNOp1p(AstNode* newp) { if (newp) setOp1p(newp); }
    void setNOp2p(AstNode* newp) { if (newp) setOp2p(newp); }
    void setNOp3p(AstNode* newp) { if (newp) setOp3p(newp); }
    void setNOp4p(AstNode* newp) { if (newp) setOp4p(newp); }

    void addOp1p(AstNode* newp);  // Append newp to end of op1
    void addOp2p(AstNode* newp);  // Append newp to end of op2
    void addOp3p(AstNode* newp);  // Append newp to end of op3
    void addOp4p(AstNode* newp);  // Append newp to end of op4

    void addNOp1p(AstNode* newp) { if (newp) addOp1p(newp); }
    void addNOp2p(AstNode* newp) { if (newp) addOp2p(newp); }
    void addNOp3p(AstNode* newp) { if (newp) addOp3p(newp); }
    void addNOp4p(AstNode* newp) { if (newp) addOp4p(newp); }

    void clonep(AstNode* nodep) { m_clonep = nodep; m_cloneCnt = s_cloneCntGbl; }
    static void cloneClearTree() { s_cloneCntGbl++; UASSERT_STATIC(s_cloneCntGbl, "Rollover"); }

public:
    // ACCESSORS
    virtual AstType type() const = 0;
    const char* typeName() const { return type().ascii(); }  // See also prettyTypeName
    AstNode* nextp() const { return m_nextp; }
    AstNode* backp() const { return m_backp; }
    AstNode* op1p() const { return m_op1p; }
    AstNode* op2p() const { return m_op2p; }
    AstNode* op3p() const { return m_op3p; }
    AstNode* op4p() const { return m_op4p; }
    AstNodeDType* dtypep() const { return m_dtypep; }
    AstNode* clonep() const { return ((m_cloneCnt==s_cloneCntGbl)?m_clonep:NULL); }
    AstNode* firstAbovep() const {  // Returns NULL when second or later in list
        return ((backp() && backp()->nextp()!=this) ? backp() : NULL); }
    bool brokeExists() const;
    bool brokeExistsAbove() const;

    // CONSTRUCTORS
    virtual ~AstNode() {}
#ifdef VL_LEAK_CHECKS
    static void* operator new(size_t size);
    static void operator delete(void* obj, size_t size);
#endif

    // CONSTANT ACCESSORS
    static int instrCountBranch() { return 4; }        ///< Instruction cycles to branch
    static int instrCountDiv() { return 10; }          ///< Instruction cycles to divide
    static int instrCountDpi() { return 1000; }        ///< Instruction cycles to call user function
    static int instrCountLd() { return 2; }            ///< Instruction cycles to load memory
    static int instrCountMul() { return 3; }           ///< Instruction cycles to multiply integers
    static int instrCountPli() { return 20; }          ///< Instruction cycles to call pli routines
    static int instrCountDouble() { return 8; }        ///< Instruction cycles to convert or do floats
    static int instrCountDoubleDiv() { return 40; }    ///< Instruction cycles to divide floats
    static int instrCountDoubleTrig() { return 200; }  ///< Instruction cycles to do trigonomics
    static int instrCountString() { return 100; }      ///< Instruction cycles to do string ops
    static int instrCountCall() { return instrCountBranch()+10; }  ///< Instruction cycles to call subroutine
    static int instrCountTime() { return instrCountCall()+5; }     ///< Instruction cycles to determine simulation time

    // ACCESSORS
    virtual string name() const { return ""; }
    virtual void name(const string& name) { this->v3fatalSrc("name() called on object without name() method"); }
    virtual void tag(const string& text) {}
    virtual string tag() const { return ""; }
    virtual string verilogKwd() const { return ""; }
    string nameProtect() const;  // Name with --protect-id applied
    string shortName() const;  // Name with __PVT__ removed for concatenating scopes
    static string dedotName(const string& namein);  // Name with dots removed
    static string prettyName(const string& namein);  // Name for printing out to the user
    static string prettyNameQ(const string& namein) {  // Quoted pretty name (for errors)
        return string("'")+prettyName(namein)+"'"; }
    static string encodeName(const string& namein);  // Encode user name into internal C representation
    static string encodeNumber(vlsint64_t num);  // Encode number into internal C representation
    static string vcdName(const string& namein);  // Name for printing out to vcd files
    string prettyName() const { return prettyName(name()); }
    string prettyNameQ() const { return prettyNameQ(name()); }
    string prettyTypeName() const;  // "VARREF" for error messages
    virtual string prettyOperatorName() const { return "operator "+prettyTypeName(); }
    FileLine* fileline() const { return m_fileline; }
    void fileline(FileLine* fl) { m_fileline = fl; }
    bool width1() const;
    int widthInstrs() const;
    void didWidth(bool flag) { m_didWidth = flag; }
    bool didWidth() const { return m_didWidth; }
    bool didWidthAndSet() { if (didWidth()) return true; didWidth(true); return false; }
    bool doingWidth() const { return m_doingWidth; }
    void doingWidth(bool flag) { m_doingWidth = flag; }
    bool protect() const { return m_protect; }
    void protect(bool flag) { m_protect = flag; }

    //TODO stomp these width functions out, and call via dtypep() instead
    int width() const;
    int widthMin() const;
    int widthMinV() const { return v3Global.widthMinUsage()==VWidthMinUsage::VERILOG_WIDTH ? widthMin() : width(); }
    int widthWords() const { return VL_WORDS_I(width()); }
    bool isQuad() const { return (width()>VL_WORDSIZE && width()<=VL_QUADSIZE); }
    bool isWide() const { return (width()>VL_QUADSIZE); }
    bool isDouble() const;
    bool isSigned() const;
    bool isString() const;

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

    vluint64_t editCount() const { return m_editCount; }
    void editCountInc() { m_editCount = ++s_editCntGbl; }  // Preincrement, so can "watch AstNode::s_editCntGbl=##"
    static vluint64_t editCountLast() { return s_editCntLast; }
    static vluint64_t editCountGbl() { return s_editCntGbl; }
    static void editCountSetLast() { s_editCntLast = editCountGbl(); }

    // ACCESSORS for specific types
    // Alas these can't be virtual or they break when passed a NULL
    bool isZero() const;
    bool isOne() const;
    bool isNeqZero() const;
    bool isAllOnes() const;
    bool isAllOnesV() const;  // Verilog width rules apply

    // METHODS - data type changes especially for initial creation
    void dtypep(AstNodeDType* nodep) { if (m_dtypep != nodep) { m_dtypep = nodep; editCountInc(); } }
    void dtypeFrom(AstNode* fromp) { if (fromp) { dtypep(fromp->dtypep()); }}
    void dtypeChgSigned(bool flag=true);
    void dtypeChgWidth(int width, int widthMin);
    void dtypeChgWidthSigned(int width, int widthMin, AstNumeric numeric);
    void dtypeSetBitUnsized(int width, int widthMin, AstNumeric numeric) {
        dtypep(findBitDType(width, widthMin, numeric)); }
    void dtypeSetBitSized(int width, AstNumeric numeric) {
        dtypep(findBitDType(width, width, numeric)); }  // Since sized, widthMin is width
    void dtypeSetLogicUnsized(int width, int widthMin, AstNumeric numeric) {
        dtypep(findLogicDType(width, widthMin, numeric)); }
    void dtypeSetLogicSized(int width, AstNumeric numeric) {
        dtypep(findLogicDType(width, width, numeric)); }  // Since sized, widthMin is width
    void dtypeSetLogicBool()     { dtypep(findLogicBoolDType()); }
    void dtypeSetDouble()        { dtypep(findDoubleDType()); }
    void dtypeSetString()        { dtypep(findStringDType()); }
    void dtypeSetSigned32()      { dtypep(findSigned32DType()); }
    void dtypeSetUInt32()        { dtypep(findUInt32DType()); }  // Twostate
    void dtypeSetUInt64()        { dtypep(findUInt64DType()); }  // Twostate

    // Data type locators
    AstNodeDType* findLogicBoolDType()  { return findBasicDType(AstBasicDTypeKwd::LOGIC); }
    AstNodeDType* findDoubleDType()     { return findBasicDType(AstBasicDTypeKwd::DOUBLE); }
    AstNodeDType* findStringDType()     { return findBasicDType(AstBasicDTypeKwd::STRING); }
    AstNodeDType* findSigned32DType()   { return findBasicDType(AstBasicDTypeKwd::INTEGER); }
    AstNodeDType* findUInt32DType()     { return findBasicDType(AstBasicDTypeKwd::UINT32); }  // Twostate
    AstNodeDType* findUInt64DType()     { return findBasicDType(AstBasicDTypeKwd::UINT64); }  // Twostate
    AstNodeDType* findBitDType(int width, int widthMin, AstNumeric numeric) const;
    AstNodeDType* findLogicDType(int width, int widthMin, AstNumeric numeric) const;
    AstNodeDType* findLogicRangeDType(VNumRange range, int widthMin, AstNumeric numeric) const;
    AstNodeDType* findBasicDType(AstBasicDTypeKwd kwd) const;
    AstBasicDType* findInsertSameDType(AstBasicDType* nodep);

    // METHODS - dump and error
    void v3errorEnd(std::ostringstream& str) const;
    void v3errorEndFatal(std::ostringstream& str) const VL_ATTR_NORETURN;
    string warnContextPrimary() const { return fileline()->warnContextPrimary(); }
    string warnContextSecondary() const { return fileline()->warnContextSecondary(); }
    string warnMore() const { return fileline()->warnMore(); }
    string warnOther() const { return fileline()->warnOther(); }

    virtual void dump(std::ostream& str=std::cout) const;
    void dumpGdb();  // For GDB only
    void dumpGdbHeader() const;

    // METHODS - Tree modifications
    static AstNode* addNext(AstNode* nodep, AstNode* newp);  // Returns nodep, adds newp to end of nodep's list
    static AstNode* addNextNull(AstNode* nodep, AstNode* newp);  // Returns nodep, adds newp (maybe NULL) to end of nodep's list
    inline AstNode* addNext(AstNode* newp) { return addNext(this, newp); }
    inline AstNode* addNextNull(AstNode* newp) { return addNextNull(this, newp); }
    void addNextHere(AstNode* newp);  // Insert newp at this->nextp
    void addPrev(AstNode* newp) { replaceWith(newp); newp->addNext(this); }
    void addHereThisAsNext(AstNode* newp);  // Adds at old place of this, this becomes next
    void replaceWith(AstNode* newp);  // Replace current node in tree with new node
    AstNode* unlinkFrBack(AstNRelinker* linkerp=NULL);  // Unlink this from whoever points to it.
    // Unlink this from whoever points to it, keep entire next list with unlinked node
    AstNode* unlinkFrBackWithNext(AstNRelinker* linkerp=NULL);
    void swapWith(AstNode* bp);
    void relink(AstNRelinker* linkerp);  // Generally use linker->relink() instead
    void cloneRelinkNode() { cloneRelink(); }
    // Iterate and insert - assumes tree format
    virtual void addNextStmt(AstNode* newp, AstNode* belowp);  // When calling, "this" is second argument
    virtual void addBeforeStmt(AstNode* newp, AstNode* belowp);  // When calling, "this" is second argument

    // METHODS - Iterate on a tree
    // Clone or return NULL if NULL
    static AstNode* cloneTreeNull(AstNode* nodep, bool cloneNextLink) {
        return nodep ? nodep->cloneTree(cloneNextLink) : NULL; }
    AstNode* cloneTree(bool cloneNextLink);  // Not const, as sets clonep() on original nodep
    bool gateTree() { return gateTreeIter(); }  // Is tree isGateOptimizable?
    bool sameTree(const AstNode* node2p) const;  // Does tree of this == node2p?
    bool sameGateTree(const AstNode* node2p) const;  // Does tree of this == node2p?, not allowing non-isGateOptimizable
    void deleteTree();  // Always deletes the next link
    void checkTree();  // User Interface version
    void checkIter() const;
    void clearIter() { m_iterpp = NULL; }
    void dumpPtrs(std::ostream& os=std::cout) const;
    void dumpTree(std::ostream& os=std::cout, const string& indent="    ", int maxDepth=0) const;
    void dumpTree(const string& indent, int maxDepth=0) const { dumpTree(cout, indent, maxDepth); }
    void dumpTreeGdb();  // For GDB only
    void dumpTreeAndNext(std::ostream& os=std::cout, const string& indent="    ", int maxDepth=0) const;
    void dumpTreeFile(const string& filename, bool append=false, bool doDump=true);
    static void dumpTreeFileGdb(const char* filenamep=NULL);

    // METHODS - queries
    virtual bool isPure() const { return true; }  // Else a $display, etc, that must be ordered with other displays
    virtual bool isBrancher() const { return false; }  // Changes control flow, disable some optimizations
    virtual bool isGateOptimizable() const { return true; }  // Else a AstTime etc that can't be pushed out
    // GateDedupable is a slightly larger superset of GateOptimzable (eg, AstNodeIf)
    virtual bool isGateDedupable() const { return isGateOptimizable(); }
    virtual bool isSubstOptimizable() const { return true; }  // Else a AstTime etc that can't be substituted out
    virtual bool isPredictOptimizable() const { return true; }  // Else a AstTime etc which output can't be predicted from input
    virtual bool isOutputter() const { return false; }  // Else creates output or exits, etc, not unconsumed
    // isUnlikely handles $stop or similar statement which means an above IF
    // statement is unlikely to be taken
    virtual bool isUnlikely() const { return false; }
    virtual int instrCount() const { return 0; }
    virtual V3Hash sameHash() const { return V3Hash(V3Hash::Illegal()); }  // Not a node that supports it
    virtual bool same(const AstNode*) const { return true; }
    virtual bool hasDType() const { return false; }  // Iff has a data type; dtype() must be non null
    virtual AstNodeDType* getChildDTypep() const { return NULL; }  // Iff has a non-null childDTypep(), as generic node function
    // Another AstNode* may have a pointer into this node, other then normal front/back/etc.
    virtual bool maybePointedTo() const { return false; }
    virtual const char* broken() const { return NULL; }

    // INVOKERS
    virtual void accept(AstNVisitor& v) = 0;

protected:
    // All AstNVisitor related functions are called as methods off the visitor
    friend class AstNVisitor;
    void iterateChildren(AstNVisitor& v);  // Use instead AstNVisitor::iterateChildren
    void iterateChildrenBackwards(AstNVisitor& v);  // Use instead AstNVisitor::iterateChildrenBackwards
    void iterateChildrenConst(AstNVisitor& v);  // Use instead AstNVisitor::iterateChildrenConst
    void iterateAndNext(AstNVisitor& v);  // Use instead AstNVisitor::iterateAndNextNull
    void iterateAndNextConst(AstNVisitor& v);  // Use instead AstNVisitor::iterateAndNextConstNull
    AstNode* iterateSubtreeReturnEdits(AstNVisitor& v);  // Use instead AstNVisitor::iterateSubtreeReturnEdits
private:
    void iterateListBackwards(AstNVisitor& v);

    // CONVERSION
public:
#include "V3Ast__gen_interface.h"  // From ./astgen
    // Things like:
    //  AstAlways*      castAlways();
};

inline std::ostream& operator<<(std::ostream& os, const AstNode* rhs) {
    if (!rhs) os<<"NULL"; else rhs->dump(os); return os;
}
inline void AstNRelinker::relink(AstNode* newp) { newp->AstNode::relink(this); }

//######################################################################
//######################################################################
//=== AstNode* : Derived generic node types

#define ASTNODE_BASE_FUNCS(name)        \
    virtual ~Ast ##name() {} \
    static Ast ##name * cloneTreeNull(Ast ##name * nodep, bool cloneNextLink) { \
        return nodep ? nodep->cloneTree(cloneNextLink) : NULL; } \
    Ast ##name * cloneTree(bool cloneNext) { return static_cast<Ast ##name *>(AstNode::cloneTree(cloneNext)); } \
    Ast ##name * clonep() const { return static_cast<Ast ##name *>(AstNode::clonep()); }

class AstNodeMath : public AstNode {
    // Math -- anything that's part of an expression tree
public:
    explicit AstNodeMath(FileLine* fl)
        : AstNode(fl) {}
    ASTNODE_BASE_FUNCS(NodeMath)
    // METHODS
    virtual bool hasDType() const { return true; }
    virtual string emitVerilog() = 0;  /// Format string for verilog writing; see V3EmitV
    virtual string emitC() = 0;
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() const = 0;  // True if output has extra upper bits zero
    // Someday we will generically support data types on every math node
    // Until then isOpaque indicates we shouldn't constant optimize this node type
    bool isOpaque() { return VN_IS(this, CvtPackString); }
};

class AstNodeTermop : public AstNodeMath {
    // Terminal operator -- a operator with no "inputs"
public:
    explicit AstNodeTermop(FileLine* fl)
        : AstNodeMath(fl) {}
    ASTNODE_BASE_FUNCS(NodeTermop)
    // Know no children, and hot function, so skip iterator for speed
    // See checkTreeIter also that asserts no children
    // cppcheck-suppress functionConst
    void iterateChildren(AstNVisitor& v) { }
};

class AstNodeUniop : public AstNodeMath {
    // Unary math
public:
    AstNodeUniop(FileLine* fl, AstNode* lhsp)
        : AstNodeMath(fl) {
        dtypeFrom(lhsp);
        setOp1p(lhsp); }
    ASTNODE_BASE_FUNCS(NodeUniop)
    AstNode* lhsp() const { return op1p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    // METHODS
    virtual void numberOperate(V3Number& out, const V3Number& lhs) = 0;  // Set out to evaluation of a AstConst'ed lhs
    virtual bool cleanLhs() const = 0;
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool doubleFlavor() const { return false; }  // D flavor of nodes with both flavors?
    virtual bool signedFlavor() const { return false; }  // Signed flavor of nodes with both flavors?
    virtual bool stringFlavor() const { return false; }  // N flavor of nodes with both flavors?
    virtual int instrCount() const { return widthInstrs(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(const AstNode*) const { return true; }
};

class AstNodeBiop : public AstNodeMath {
    // Binary math
public:
    AstNodeBiop(FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeMath(fl) {
        setOp1p(lhs); setOp2p(rhs); }
    ASTNODE_BASE_FUNCS(NodeBiop)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) = 0;  // Clone single node, just get same type back.
    // ACCESSORS
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    // METHODS
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) = 0;  // Set out to evaluation of a AstConst'ed
    virtual bool cleanLhs() const = 0;  // True if LHS must have extra upper bits zero
    virtual bool cleanRhs() const = 0;  // True if RHS must have extra upper bits zero
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool sizeMattersRhs() const = 0;  // True if output result depends on rhs size
    virtual bool doubleFlavor() const { return false; }  // D flavor of nodes with both flavors?
    virtual bool signedFlavor() const { return false; }  // Signed flavor of nodes with both flavors?
    virtual bool stringFlavor() const { return false; }  // N flavor of nodes with both flavors?
    virtual int instrCount() const { return widthInstrs(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(const AstNode*) const { return true; }
};

class AstNodeTriop : public AstNodeMath {
    // Trinary math
public:
    AstNodeTriop(FileLine* fl, AstNode* lhs, AstNode* rhs, AstNode* ths)
        : AstNodeMath(fl) {
        setOp1p(lhs); setOp2p(rhs); setOp3p(ths); }
    ASTNODE_BASE_FUNCS(NodeTriop)
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    AstNode* thsp() const { return op3p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    void thsp(AstNode* nodep) { return setOp3p(nodep); }
    // METHODS
    // Set out to evaluation of a AstConst'ed
    virtual void numberOperate(V3Number& out, const V3Number& lhs,
                               const V3Number& rhs, const V3Number& ths) = 0;
    virtual bool cleanLhs() const = 0;  // True if LHS must have extra upper bits zero
    virtual bool cleanRhs() const = 0;  // True if RHS must have extra upper bits zero
    virtual bool cleanThs() const = 0;  // True if THS must have extra upper bits zero
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool sizeMattersRhs() const = 0;  // True if output result depends on rhs size
    virtual bool sizeMattersThs() const = 0;  // True if output result depends on ths size
    virtual int instrCount() const { return widthInstrs(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(const AstNode*) const { return true; }
};

class AstNodeBiCom : public AstNodeBiop {
    // Binary math with commutative properties
public:
    AstNodeBiCom(FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeBiop(fl, lhs, rhs) {}
    ASTNODE_BASE_FUNCS(NodeBiCom)
};

class AstNodeBiComAsv : public AstNodeBiCom {
    // Binary math with commutative & associative properties
public:
    AstNodeBiComAsv(FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeBiCom(fl, lhs, rhs) {}
    ASTNODE_BASE_FUNCS(NodeBiComAsv)
};
class AstNodeCond : public AstNodeTriop {
public:
    AstNodeCond(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
        : AstNodeTriop(fl, condp, expr1p, expr2p) {
        if (expr1p) dtypeFrom(expr1p);
        else if (expr2p) dtypeFrom(expr2p);
    }
    ASTNODE_BASE_FUNCS(NodeCond)
    virtual void numberOperate(V3Number& out, const V3Number& lhs,
                               const V3Number& rhs, const V3Number& ths);
    AstNode* condp() const { return op1p(); }  // op1 = Condition
    AstNode* expr1p() const { return op2p(); }  // op2 = If true...
    AstNode* expr2p() const { return op3p(); }  // op3 = If false...
    virtual string emitVerilog() { return "%k(%l %f? %r %k: %t)"; }
    virtual string emitC() { return "VL_COND_%nq%lq%rq%tq(%nw,%lw,%rw,%tw, %P, %li, %ri, %ti)"; }
    virtual bool cleanOut() const { return false; }  // clean if e1 & e2 clean
    virtual bool cleanLhs() const { return true; }
    virtual bool cleanRhs() const { return false; }
    virtual bool cleanThs() const { return false; }  // Propagates up
    virtual bool sizeMattersLhs() const { return false; }
    virtual bool sizeMattersRhs() const { return false; }
    virtual bool sizeMattersThs() const { return false; }
    virtual int instrCount() const { return instrCountBranch(); }
    virtual AstNode* cloneType(AstNode* condp, AstNode* expr1p, AstNode* expr2p) = 0;
};

class AstNodePreSel : public AstNode {
    // Something that becomes an AstSel
public:
    AstNodePreSel(FileLine* fl, AstNode* lhs, AstNode* rhs, AstNode* ths)
        : AstNode(fl) {
        setOp1p(lhs); setOp2p(rhs); setNOp3p(ths); }
    ASTNODE_BASE_FUNCS(NodePreSel)
    AstNode* lhsp() const { return op1p(); }
    AstNode* fromp() const { return lhsp(); }
    AstNode* rhsp() const { return op2p(); }
    AstNode* thsp() const { return op3p(); }
    AstAttrOf* attrp() const { return VN_CAST(op4p(), AttrOf); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    void thsp(AstNode* nodep) { return setOp3p(nodep); }
    void attrp(AstAttrOf* nodep) { return setOp4p((AstNode*)nodep); }
    // METHODS
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(const AstNode*) const { return true; }
};

class AstNodeStmt : public AstNode {
    // Statement -- anything that's directly under a function
public:
    explicit AstNodeStmt(FileLine* fl)
        : AstNode(fl) {}
    ASTNODE_BASE_FUNCS(NodeStmt)
    // METHODS
    virtual bool isStatement() const { return true; }  // Really a statement
    virtual void addNextStmt(AstNode* newp, AstNode* belowp);  // Stop statement searchback here
    virtual void addBeforeStmt(AstNode* newp, AstNode* belowp);  // Stop statement searchback here
};

class AstNodeAssign : public AstNodeStmt {
public:
    AstNodeAssign(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : AstNodeStmt(fl) {
        setOp1p(rhsp); setOp2p(lhsp);
        dtypeFrom(lhsp);
    }
    ASTNODE_BASE_FUNCS(NodeAssign)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) = 0;  // Clone single node, just get same type back.
    // So iteration hits the RHS which is "earlier" in execution order, it's op1, not op2
    AstNode* rhsp() const { return op1p(); }  // op1 = Assign from
    AstNode* lhsp() const { return op2p(); }  // op2 = Assign to
    void rhsp(AstNode* np) { setOp1p(np); }
    void lhsp(AstNode* np) { setOp2p(np); }
    virtual bool hasDType() const { return true; }
    virtual bool cleanRhs() const { return true; }
    virtual int instrCount() const { return widthInstrs(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(const AstNode*) const { return true; }
    virtual string verilogKwd() const { return "="; }
    virtual bool brokeLhsMustBeLvalue() const = 0;
};

class AstNodeFor : public AstNodeStmt {
public:
    AstNodeFor(FileLine* fileline, AstNode* initsp, AstNode* condp,
               AstNode* incsp, AstNode* bodysp)
        : AstNodeStmt(fileline) {
        addNOp1p(initsp); setOp2p(condp); addNOp3p(incsp); addNOp4p(bodysp);
    }
    ASTNODE_BASE_FUNCS(NodeFor)
    AstNode* initsp() const { return op1p(); }  // op1 = initial statements
    AstNode* condp() const { return op2p(); }  // op2 = condition to continue
    AstNode* incsp() const { return op3p(); }  // op3 = increment statements
    AstNode* bodysp() const { return op4p(); }  // op4 = body of loop
    virtual bool isGateOptimizable() const { return false; }
    virtual int instrCount() const { return instrCountBranch(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(const AstNode* samep) const { return true; }
};

class AstNodeIf : public AstNodeStmt {
private:
    VBranchPred m_branchPred;  // Branch prediction as taken/untaken?
public:
    AstNodeIf(FileLine* fl, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
        : AstNodeStmt(fl) {
        setOp1p(condp); addNOp2p(ifsp); addNOp3p(elsesp);
    }
    ASTNODE_BASE_FUNCS(NodeIf)
    AstNode* condp() const { return op1p(); }  // op1 = condition
    AstNode* ifsp() const { return op2p(); }  // op2 = list of true statements
    AstNode* elsesp() const { return op3p(); }  // op3 = list of false statements
    void condp(AstNode* newp) { setOp1p(newp); }
    void addIfsp(AstNode* newp) { addOp2p(newp); }
    void addElsesp(AstNode* newp) { addOp3p(newp); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isGateDedupable() const { return true; }
    virtual int instrCount() const { return instrCountBranch(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(const AstNode* samep) const { return true; }
    void branchPred(VBranchPred flag) { m_branchPred = flag; }
    VBranchPred branchPred() const { return m_branchPred; }
};

class AstNodeCase : public AstNodeStmt {
public:
    AstNodeCase(FileLine* fl, AstNode* exprp, AstNode* casesp)
        : AstNodeStmt(fl) {
        setOp1p(exprp); addNOp2p(casesp);
    }
    ASTNODE_BASE_FUNCS(NodeCase)
    virtual int instrCount() const { return instrCountBranch(); }
    AstNode* exprp() const { return op1p(); }  // op1 = case condition <expression>
    AstCaseItem* itemsp() const { return VN_CAST(op2p(), CaseItem); }  // op2 = list of case expressions
    AstNode* notParallelp() const { return op3p(); }  // op3 = assertion code for non-full case's
    void addItemsp(AstNode* nodep) { addOp2p(nodep); }
    void addNotParallelp(AstNode* nodep) { setOp3p(nodep); }
};

class AstNodeSenItem : public AstNode {
    // An AstSenItem or AstSenGate
public:
    explicit AstNodeSenItem(FileLine* fl) : AstNode(fl) {}
    ASTNODE_BASE_FUNCS(NodeSenItem)
    virtual bool isClocked() const = 0;
    virtual bool isCombo() const = 0;
    virtual bool isInitial() const = 0;
    virtual bool isSettle() const = 0;
    virtual bool isNever() const = 0;
};

class AstNodeVarRef : public AstNodeMath {
    // An AstVarRef or AstVarXRef
private:
    bool        m_lvalue;       // Left hand side assignment
    AstVar*     m_varp;         // [AfterLink] Pointer to variable itself
    AstVarScope* m_varScopep;   // Varscope for hierarchy
    AstPackage* m_packagep;     // Package hierarchy
    string      m_name;         // Name of variable
    string      m_hiername;     // Scope converted into name-> for emitting
    bool        m_hierThis;     // Hiername points to "this" function
    void init();
public:
    AstNodeVarRef(FileLine* fl, const string& name, bool lvalue)
        : AstNodeMath(fl), m_lvalue(lvalue), m_varp(NULL), m_varScopep(NULL),
          m_packagep(NULL), m_name(name), m_hierThis(false) {
        init();
    }
    AstNodeVarRef(FileLine* fl, const string& name, AstVar* varp, bool lvalue)
        : AstNodeMath(fl), m_lvalue(lvalue), m_varp(varp), m_varScopep(NULL),
          m_packagep(NULL), m_name(name), m_hierThis(false) {
        // May have varp==NULL
        init();
    }
    ASTNODE_BASE_FUNCS(NodeVarRef)
    virtual bool hasDType() const { return true; }
    virtual const char* broken() const;
    virtual int instrCount() const { return widthInstrs(); }
    virtual void cloneRelink();
    virtual string name() const { return m_name; }  // * = Var name
    virtual void name(const string& name) { m_name = name; }
    bool lvalue() const { return m_lvalue; }
    void lvalue(bool lval) { m_lvalue = lval; }  // Avoid using this; Set in constructor
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    void varp(AstVar* varp) { m_varp = varp; }
    AstVarScope* varScopep() const { return m_varScopep; }
    void varScopep(AstVarScope* varscp) { m_varScopep = varscp; }
    string hiername() const { return m_hiername; }
    string hiernameProtect() const;
    void hiername(const string& hn) { m_hiername = hn; }
    bool hierThis() const { return m_hierThis; }
    void hierThis(bool flag) { m_hierThis = flag; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }
    // Know no children, and hot function, so skip iterator for speed
    // See checkTreeIter also that asserts no children
    // cppcheck-suppress functionConst
    void iterateChildren(AstNVisitor& v) { }
};

class AstNodeText : public AstNode {
private:
    string      m_text;
public:
    // Node that simply puts text into the output stream
    AstNodeText(FileLine* fileline, const string& textp)
        : AstNode(fileline) {
        m_text = textp;  // Copy it
    }
    ASTNODE_BASE_FUNCS(NodeText)
    virtual void dump(std::ostream& str=std::cout) const;
    virtual V3Hash sameHash() const { return V3Hash(text()); }
    virtual bool same(const AstNode* samep) const {
        const AstNodeText* asamep = static_cast<const AstNodeText*>(samep);
        return text() == asamep->text(); }
    const string& text() const { return m_text; }
};

class AstNodeDType : public AstNode {
    // Ideally width() would migrate to BasicDType as that's where it makes sense,
    // but it's currently so prevalent in the code we leave it here.
    // Note the below members are included in AstTypeTable::Key lookups
private:
    int         m_width;        // (also in AstTypeTable::Key) Bit width of operation
    int         m_widthMin;     // (also in AstTypeTable::Key) If unsized, bitwidth of minimum implementation
    AstNumeric  m_numeric;      // (also in AstTypeTable::Key) Node is signed
    // Other members
    bool        m_generic;      // Simple globally referenced type, don't garbage collect
    static int  s_uniqueNum;    // Unique number assigned to each dtype during creation for IEEE matching
public:
    // CONSTRUCTORS
    explicit AstNodeDType(FileLine* fl) : AstNode(fl) {
        m_width = 0; m_widthMin = 0; m_generic = false;
    }
    ASTNODE_BASE_FUNCS(NodeDType)
    // ACCESSORS
    virtual void dump(std::ostream& str) const;
    virtual void dumpSmall(std::ostream& str) const;
    virtual bool hasDType() const { return true; }
    virtual AstBasicDType* basicp() const = 0;  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const = 0;  // recurses over typedefs/const/enum to next non-typeref type
    virtual AstNodeDType* skipRefToConstp() const = 0;  // recurses over typedefs to next non-typeref-or-const type
    virtual AstNodeDType* skipRefToEnump() const = 0;  // recurses over typedefs/const to next non-typeref-or-enum/struct type
    virtual int widthAlignBytes() const = 0;  // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthTotalBytes() const = 0;  // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    virtual bool maybePointedTo() const { return true; }
    virtual AstNodeDType* virtRefDTypep() const { return NULL; }  // Iff has a non-null refDTypep(), as generic node function
    virtual void virtRefDTypep(AstNodeDType* nodep) { }  // Iff has refDTypep(), set as generic node function
    virtual bool similarDType(AstNodeDType* samep) const = 0;  // Assignable equivalence.  Call skipRefp() on this and samep before calling
    virtual AstNodeDType* subDTypep() const { return NULL; }  // Iff has a non-null subDTypep(), as generic node function
    virtual bool isFourstate() const;
    //
    // Changing the width may confuse the data type resolution, so must clear
    // TypeTable cache after use.
    void widthForce(int width, int widthMin) { m_width = width; m_widthMin = widthMin; }
    // For backward compatibility inherit width and signing from the subDType/base type
    void widthFromSub(AstNodeDType* nodep) { m_width = nodep->m_width; m_widthMin = nodep->m_widthMin; m_numeric = nodep->m_numeric; }
    //
    int width() const { return m_width; }
    void numeric(AstNumeric flag) { m_numeric = flag; }
    bool isSigned() const { return m_numeric.isSigned(); }
    bool isNosign() const { return m_numeric.isNosign(); }
    AstNumeric numeric() const { return m_numeric; }
    int widthWords() const { return VL_WORDS_I(width()); }
    int widthMin() const {  // If sized, the size, if unsized the min digits to represent it
        return m_widthMin?m_widthMin:m_width; }
    int widthPow2() const;
    void widthMinFromWidth() { m_widthMin = m_width; }
    bool widthSized() const { return !m_widthMin || m_widthMin==m_width; }
    bool generic() const { return m_generic; }
    void generic(bool flag) { m_generic = flag; }
    AstNodeDType* dtypeDimensionp(int dimension);
    std::pair<uint32_t,uint32_t> dimensions(bool includeBasic);
    uint32_t arrayUnpackedElements();  // 1, or total multiplication of all dimensions
    static int uniqueNumInc() { return ++s_uniqueNum; }
    const char* charIQWN() const { return (isString() ? "N" : isWide() ? "W" : isQuad() ? "Q" : "I"); }
};

class AstNodeClassDType : public AstNodeDType {
private:
    // TYPES
    typedef std::map<string,AstMemberDType*> MemberNameMap;
    // MEMBERS
    string m_name;  // Name from upper typedef, if any
    bool                m_packed;
    bool                m_isFourstate;
    MemberNameMap       m_members;
public:
    AstNodeClassDType(FileLine* fl, AstNumeric numericUnpack)
        : AstNodeDType(fl) {
        // AstNumeric::NOSIGN overloaded to indicate not packed
        m_packed = (numericUnpack != AstNumeric::NOSIGN);
        m_isFourstate = false;  // V3Width computes
        numeric(AstNumeric::fromBool(numericUnpack.isSigned()));
    }
    ASTNODE_BASE_FUNCS(NodeClassDType)
    virtual const char* broken() const;
    virtual void dump(std::ostream& str) const;
    // For basicp() we reuse the size to indicate a "fake" basic type of same size
    virtual AstBasicDType* basicp() const {
        return (isFourstate()
                ? VN_CAST(findLogicDType(width(), width(), numeric()), BasicDType)
                : VN_CAST(findBitDType(width(), width(), numeric()), BasicDType)); }
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const;  // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthTotalBytes() const;  // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    // op1 = members
    virtual bool similarDType(AstNodeDType* samep) const {
        return this==samep;  // We don't compare members, require exact equivalence
    }
    virtual string name() const { return m_name; }
    void name(const string& flag) { m_name = flag; }
    AstMemberDType* membersp() const { return VN_CAST(op1p(), MemberDType); }  // op1 = AstMember list
    void addMembersp(AstNode* nodep) { addNOp1p(nodep); }
    bool packed() const { return m_packed; }
    bool packedUnsup() const { return true; }  // packed() but as don't support unpacked, presently all structs
    void isFourstate(bool flag) { m_isFourstate = flag; }
    virtual bool isFourstate() const { return m_isFourstate; }
    void clearCache() { m_members.clear(); }
    void repairMemberCache();
    AstMemberDType* findMember(const string& name) const {
        MemberNameMap::const_iterator it = m_members.find(name);
        return (it==m_members.end()) ? NULL : it->second;
    }
    int lsb() const { return 0; }
    int msb() const { return dtypep()->width()-1; }  // Packed classes look like arrays
    VNumRange declRange() const { return VNumRange(msb(), lsb(), false); }
};

class AstNodeArrayDType : public AstNodeDType {
    // Array data type, ie "some_dtype var_name [2:0]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: RANGE (array bounds)
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
    AstNode* rangenp() const { return op2p(); }  // op2 = Array(s) of variable
public:
    explicit AstNodeArrayDType(FileLine* fl) : AstNodeDType(fl) {
        m_refDTypep = NULL;
    }
    ASTNODE_BASE_FUNCS(NodeArrayDType)
    virtual void dump(std::ostream& str) const;
    virtual void dumpSmall(std::ostream& str) const;
    virtual const char* broken() const {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep()))); return NULL; }
    virtual void cloneRelink() { if (m_refDTypep && m_refDTypep->clonep()) {
        m_refDTypep = m_refDTypep->clonep();
    }}
    virtual bool same(const AstNode* samep) const {
        const AstNodeArrayDType* asamep = static_cast<const AstNodeArrayDType*>(samep);
        return (msb()==asamep->msb()
                && subDTypep()==asamep->subDTypep()
                && rangenp()->sameTree(asamep->rangenp())); }  // HashedDT doesn't recurse, so need to check children
    virtual bool similarDType(AstNodeDType* samep) const {
        const AstNodeArrayDType* asamep = static_cast<const AstNodeArrayDType*>(samep);
        return (asamep
                && type() == samep->type()
                && msb() == asamep->msb()
                && rangenp()->sameTree(asamep->rangenp())
                && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp()));
    }
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(m_refDTypep), V3Hash(msb()), V3Hash(lsb())); }
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }  // op1 = Range of variable
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const { return m_refDTypep ? m_refDTypep : childDTypep(); }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) { refDTypep(nodep); }
    AstRange* rangep() const { return VN_CAST(op2p(), Range); }  // op2 = Array(s) of variable
    void rangep(AstRange* nodep);
    // METHODS
    virtual AstBasicDType* basicp() const { return subDTypep()->basicp(); }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return elementsConst() * subDTypep()->widthTotalBytes(); }
    int msb() const;
    int lsb() const;
    int elementsConst() const;
    VNumRange declRange() const;
};

class AstNodeSel : public AstNodeBiop {
    // Single bit range extraction, perhaps with non-constant selection or array selection
public:
    AstNodeSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : AstNodeBiop(fl, fromp, bitp) {}
    ASTNODE_BASE_FUNCS(NodeSel)
    AstNode* fromp() const { return op1p(); }  // op1 = Extracting what (NULL=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* bitp() const { return op2p(); }  // op2 = Msb selection expression
    void bitp(AstNode* nodep) { setOp2p(nodep); }
    int bitConst() const;
    virtual bool hasDType() const { return true; }
};

class AstNodeStream : public AstNodeBiop {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstNodeStream(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
        if (lhsp->dtypep()) {
            dtypeSetLogicSized(lhsp->dtypep()->width(), AstNumeric::UNSIGNED);
        }
    }
    ASTNODE_BASE_FUNCS(NodeStream)
};

//######################################################################
// Tasks/functions common handling

class AstNodeFTask : public AstNode {
private:
    string      m_name;         // Name of task
    string      m_cname;        // Name of task if DPI import
    uint64_t    m_dpiOpenParent;  // DPI import open array, if !=0, how many callees
    bool        m_taskPublic:1;  // Public task
    bool        m_attrIsolateAssign:1;// User isolate_assignments attribute
    bool        m_prototype:1;  // Just a prototype
    bool        m_dpiExport:1;  // DPI exported
    bool        m_dpiImport:1;  // DPI imported
    bool        m_dpiContext:1;  // DPI import context
    bool        m_dpiOpenChild:1;  // DPI import open array child wrapper
    bool        m_dpiTask:1;    // DPI import task (vs. void function)
    bool        m_pure:1;       // DPI import pure
public:
    AstNodeFTask(FileLine* fileline, const string& name, AstNode* stmtsp)
        : AstNode(fileline)
        , m_name(name)
        , m_dpiOpenParent(0), m_taskPublic(false)
        , m_attrIsolateAssign(false), m_prototype(false)
        , m_dpiExport(false), m_dpiImport(false), m_dpiContext(false)
        , m_dpiOpenChild(false), m_dpiTask(false), m_pure(false) {
        addNOp3p(stmtsp);
        cname(name);  // Might be overridden by dpi import/export
    }
    ASTNODE_BASE_FUNCS(NodeFTask)
    virtual void dump(std::ostream& str=std::cout) const;
    virtual string name() const { return m_name; }  // * = Var name
    virtual bool maybePointedTo() const { return true; }
    virtual bool isGateOptimizable() const { return !((m_dpiExport || m_dpiImport) && !m_pure); }
    // {AstFunc only} op1 = Range output variable
    virtual void name(const string& name) { m_name = name; }
    string cname() const { return m_cname; }
    void cname(const string& cname) { m_cname = cname; }
    // op1 = Output variable (functions only, NULL for tasks)
    AstNode* fvarp() const { return op1p(); }
    void addFvarp(AstNode* nodep) { addNOp1p(nodep); }
    bool isFunction() const { return fvarp()!=NULL; }
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
    void pure(bool flag) { m_pure = flag; }
    bool pure() const { return m_pure; }
};

class AstNodeFTaskRef : public AstNodeStmt {
    // A reference to a task (or function)
    // Functions are not statements, while tasks are. AstNodeStmt needs isStatement() to deal.
private:
    AstNodeFTask*       m_taskp;        // [AfterLink] Pointer to task referenced
    string              m_name;         // Name of variable
    string              m_dotted;       // Dotted part of scope the name()ed task/func is under or ""
    string              m_inlinedDots;  // Dotted hierarchy flattened out
    AstPackage*         m_packagep;     // Package hierarchy
public:
    AstNodeFTaskRef(FileLine* fl, AstNode* namep, AstNode* pinsp)
        : AstNodeStmt(fl)
        , m_taskp(NULL), m_packagep(NULL) {
        setOp1p(namep); addNOp2p(pinsp);
    }
    AstNodeFTaskRef(FileLine* fl, const string& name, AstNode* pinsp)
        : AstNodeStmt(fl)
        , m_taskp(NULL), m_name(name), m_packagep(NULL) {
        addNOp2p(pinsp);
    }
    ASTNODE_BASE_FUNCS(NodeFTaskRef)
    virtual const char* broken() const { BROKEN_RTN(m_taskp && !m_taskp->brokeExists()); return NULL; }
    virtual void cloneRelink() { if (m_taskp && m_taskp->clonep()) {
        m_taskp = m_taskp->clonep();
    }}
    virtual void dump(std::ostream& str=std::cout) const;
    virtual string name() const { return m_name; }  // * = Var name
    virtual bool isGateOptimizable() const { return m_taskp && m_taskp->isGateOptimizable(); }
    string dotted() const { return m_dotted; }  // * = Scope name or ""
    string prettyDotted() const { return prettyName(dotted()); }
    string inlinedDots() const { return m_inlinedDots; }
    void inlinedDots(const string& flag) { m_inlinedDots = flag; }
    AstNodeFTask* taskp() const { return m_taskp; }  // [After Link] Pointer to variable
    void taskp(AstNodeFTask* taskp) { m_taskp = taskp; }
    virtual void name(const string& name) { m_name = name; }
    void dotted(const string& name) { m_dotted = name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }
    // op1 = namep
    AstNode* namep() const { return op1p(); }
    // op2 = Pin interconnection list
    AstNode* pinsp() const { return op2p(); }
    void addPinsp(AstNode* nodep) { addOp2p(nodep); }
    // op3 = scope tracking
    AstScopeName* scopeNamep() const { return VN_CAST(op3p(), ScopeName); }
    void scopeNamep(AstNode* nodep) { setNOp3p(nodep); }
};

class AstNodeModule : public AstNode {
    // A module, package, program or interface declaration;
    // something that can live directly under the TOP,
    // excluding $unit package stuff
private:
    string      m_name;         // Name of the module
    string      m_origName;     // Name of the module, ignoring name() changes, for dot lookup
    string      m_hierName;     // Hierarchical name for errors, etc.
    bool        m_modPublic:1;  // Module has public references
    bool        m_modTrace:1;   // Tracing this module
    bool        m_inLibrary:1;  // From a library, no error if not used, never top level
    bool        m_dead:1;       // LinkDot believes is dead; will remove in Dead visitors
    bool        m_internal:1;   // Internally created
    bool        m_recursive:1;  // Recursive module
    bool        m_recursiveClone:1;  // If recursive, what module it clones, otherwise NULL
    int         m_level;        // 1=top module, 2=cell off top module, ...
    int         m_varNum;       // Incrementing variable number
    int         m_typeNum;      // Incrementing implicit type number
public:
    AstNodeModule(FileLine* fl, const string& name)
        : AstNode(fl)
        , m_name(name), m_origName(name)
        , m_modPublic(false), m_modTrace(false), m_inLibrary(false), m_dead(false)
        , m_internal(false), m_recursive(false), m_recursiveClone(false)
        , m_level(0), m_varNum(0), m_typeNum(0) { }
    ASTNODE_BASE_FUNCS(NodeModule)
    virtual void dump(std::ostream& str) const;
    virtual bool maybePointedTo() const { return true; }
    virtual string name() const { return m_name; }
    AstNode* stmtsp() const { return op2p(); }  // op2 = List of statements
    AstActive* activesp() const { return VN_CAST(op3p(), Active); }  // op3 = List of i/sblocks
    // METHODS
    void addInlinesp(AstNode* nodep) { addOp1p(nodep); }
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    void addActivep(AstNode* nodep) { addOp3p(nodep); }
    // ACCESSORS
    virtual void name(const string& name) { m_name = name; }
    string origName() const { return m_origName; }
    string hierName() const    { return m_hierName; }
    void hierName(const string& hierName) { m_hierName = hierName; }
    bool inLibrary() const { return m_inLibrary; }
    void inLibrary(bool flag) { m_inLibrary = flag; }
    void level(int level) { m_level = level; }
    int level() const { return m_level; }
    bool isTop() const { return level()==1; }
    int varNumGetInc() { return ++m_varNum; }
    int typeNumGetInc() { return ++m_typeNum; }
    void modPublic(bool flag) { m_modPublic = flag; }
    bool modPublic() const { return m_modPublic; }
    void modTrace(bool flag) { m_modTrace = flag; }
    bool modTrace() const { return m_modTrace; }
    void dead(bool flag) { m_dead = flag; }
    bool dead() const { return m_dead; }
    void internal(bool flag) { m_internal = flag; }
    bool internal() const { return m_internal; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
    void recursiveClone(bool flag) { m_recursiveClone = flag; }
    bool recursiveClone() const { return m_recursiveClone; }
};

class AstNodeRange : public AstNode {
    // A range, sized or unsized
public:
    explicit AstNodeRange(FileLine* fl) : AstNode(fl) { }
    ASTNODE_BASE_FUNCS(NodeRange)
};

//######################################################################

#include "V3AstNodes.h"

#include "V3Ast__gen_impl.h"  // From ./astgen
// Things like:
//  inline AstAlways* AstNode::castAlways() { return dynamic_cast<AstAlways*>(this); }
//  inline bool AstNode::privateIsaAlways(const AstNode* nodep) { return nodep && nodep->type() == AstType::atAlways; }

//######################################################################
// Inline AstNVisitor METHODS

inline void AstNVisitor::iterate(AstNode* nodep) {
    nodep->accept(*this);
}
inline void AstNVisitor::iterateChildren(AstNode* nodep) {
    nodep->iterateChildren(*this);
}
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
// Inline ACCESSORS

inline int AstNode::width() const { return dtypep() ? dtypep()->width() : 0; }
inline int AstNode::widthMin() const { return dtypep() ? dtypep()->widthMin() : 0; }
inline bool AstNode::width1() const {  // V3Const uses to know it can optimize
    return dtypep() && dtypep()->width()==1; }
inline int AstNode::widthInstrs() const {
    return (!dtypep() ? 1 : (dtypep()->isWide() ? dtypep()->widthWords() : 1)); }
inline bool AstNode::isDouble() const {
    return dtypep() && VN_IS(dtypep(), BasicDType) && VN_CAST(dtypep(), BasicDType)->isDouble(); }
inline bool AstNode::isString() const {
    return dtypep() && dtypep()->basicp() && dtypep()->basicp()->isString(); }
inline bool AstNode::isSigned() const {
    return dtypep() && dtypep()->isSigned(); }

inline bool AstNode::isZero() const     { return (VN_IS(this, Const) && VN_CAST_CONST(this, Const)->num().isEqZero()); }
inline bool AstNode::isNeqZero() const  { return (VN_IS(this, Const) && VN_CAST_CONST(this, Const)->num().isNeqZero()); }
inline bool AstNode::isOne() const      { return (VN_IS(this, Const) && VN_CAST_CONST(this, Const)->num().isEqOne()); }
inline bool AstNode::isAllOnes() const  { return (VN_IS(this, Const) && VN_CAST_CONST(this, Const)->isEqAllOnes()); }
inline bool AstNode::isAllOnesV() const { return (VN_IS(this, Const) && VN_CAST_CONST(this, Const)->isEqAllOnesV()); }
inline bool AstNode::sameTree(const AstNode* node2p) const {
    return sameTreeIter(this, node2p, true, false); }
inline bool AstNode::sameGateTree(const AstNode* node2p) const {
    return sameTreeIter(this, node2p, true, true); }

inline void AstNodeVarRef::init() { if (m_varp) dtypep(m_varp->dtypep()); }

inline bool AstNodeDType::isFourstate() const { return basicp()->isFourstate(); }

inline void AstNodeArrayDType::rangep(AstRange* nodep) { setOp2p(nodep); }
inline int AstNodeArrayDType::msb() const { return rangep()->msbConst(); }
inline int AstNodeArrayDType::lsb() const { return rangep()->lsbConst(); }
inline int AstNodeArrayDType::elementsConst() const { return rangep()->elementsConst(); }
inline VNumRange AstNodeArrayDType::declRange() const { return VNumRange(msb(), lsb(), rangep()->littleEndian()); }

inline void AstIfaceRefDType::cloneRelink() {
    if (m_cellp && m_cellp->clonep()) m_cellp = m_cellp->clonep();
    if (m_ifacep && m_ifacep->clonep()) m_ifacep = m_ifacep->clonep();
    if (m_modportp && m_modportp->clonep()) m_modportp = m_modportp->clonep(); }

#endif  // Guard
