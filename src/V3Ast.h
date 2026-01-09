// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
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
#include <cstdint>
#include <functional>
#include <map>
#include <set>
#include <type_traits>
#include <unordered_set>
#include <utility>
#include <vector>

// clang-format off
#include "V3AstAttr.h"
// clang-format on

// Forward declarations
class V3Graph;
class ExecMTask;

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
#define VN_IS(nodep, nodetypename) (AstNode::is<Ast##nodetypename>(nodep))

// (V)erilator (N)ode cast: Similar to dynamic_cast, but more efficient, use this instead.
// Cast to given type if node is of such type, otherwise returns nullptr. If 'nodep' is nullptr,
// return nullptr. Pointer constness is preserved, i.e.: given a 'const AstNode*',
// a 'const Ast<nodetypename>*' is returned.
#define VN_CAST(nodep, nodetypename) (AstNode::cast<Ast##nodetypename>(nodep))

// (V)erilator (N)ode as: Assert node is of given type then cast to that type. Use this to
// downcast instead of VN_CAST when you know the true type of the node. If 'nodep' is nullptr,
// return nullptr. Pointer constness is preserved, i.e.: given a 'const AstNode*', a 'const
// Ast<nodetypename>*' is returned.
#define VN_AS(nodep, nodetypename) (AstNode::as<Ast##nodetypename>(nodep))

// Same as VN_AS, but only checks the type in debug builds. Type checking is less critical in node
// child getters (the strongly-typed functions that wrap op*p pointers). This is because the op*p
// pointers are usually populated by code that already asserts the correct type. Having fewer type
// assertions yields better performance in release builds.
#if defined(VL_DEBUG) || defined(VL_ASAN)
#define VN_DBG_AS(nodep, nodetypename) VN_AS(nodep, nodetypename)
#else
#define VN_DBG_AS(nodep, nodetypename) (AstNode::unsafePrivateAs<Ast##nodetypename>(nodep))
#endif

// (V)erilator (N)ode deleted: Pointer to deleted AstNode (for assertions only)
#define VN_DELETED(nodep) VL_UNLIKELY(reinterpret_cast<uint64_t>(nodep) == 0x1)

//######################################################################

struct VNTypeInfo final {
    const char* m_namep;
    enum uint8_t {
        OP_UNUSED,
        OP_USED,
        OP_LIST,
        OP_OPTIONAL,
    } m_opType[4];
    const char* m_opNamep[4];
    size_t m_sizeof;
};

class VNType final {
    static const VNTypeInfo s_typeInfoTable[];

public:
#include "V3Ast__gen_type_enum.h"  // From ./astgen
    const en m_e;
    VNType() = delete;

    // VNType is interconvetible with VNType::en
    // cppcheck-suppress noExplicitConstructor
    constexpr VNType(en _e) VL_MT_SAFE : m_e{_e} {}
    constexpr operator en() const VL_MT_SAFE { return m_e; }

    // Retrieve VNTypeInfo for the given type
    static const VNTypeInfo& typeInfo(VNType t) VL_MT_SAFE { return s_typeInfoTable[t.m_e]; }
};
constexpr bool operator==(const VNType& lhs, const VNType& rhs) VL_PURE {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VNType& lhs, VNType::en rhs) VL_PURE { return lhs.m_e == rhs; }
constexpr bool operator==(VNType::en lhs, const VNType& rhs) VL_PURE { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VNType& rhs) { return os << rhs.ascii(); }

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
    template <typename T>
    typename std::enable_if<std::is_pointer<T>::value, T>::type to() const VL_MT_SAFE {
        return reinterpret_cast<T>(m_u.up);
    }
    VSymEnt* toSymEnt() const { return to<VSymEnt*>(); }
    AstNode* toNodep() const VL_MT_SAFE { return to<AstNode*>(); }
    V3GraphVertex* toGraphVertex() const { return to<V3GraphVertex*>(); }
    int toInt() const { return m_u.ui; }
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
    static uint32_t s_userCntGbl;  // Count of which usage of userp() this is
    static bool s_userBusy;  // Count is in use
public:
    VNUser1InUse()      { allocate(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser1InUse()     { free    (1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(1, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class VNUser2InUse final : VNUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t s_userCntGbl;  // Count of which usage of userp() this is
    static bool s_userBusy;  // Count is in use
public:
    VNUser2InUse()      { allocate(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser2InUse()     { free    (2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(2, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class VNUser3InUse final : VNUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t s_userCntGbl;  // Count of which usage of userp() this is
    static bool s_userBusy;  // Count is in use
public:
    VNUser3InUse()      { allocate(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser3InUse()     { free    (3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(3, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
};
class VNUser4InUse final : VNUserInUseBase {
protected:
    friend class AstNode;
    static uint32_t s_userCntGbl;  // Count of which usage of userp() this is
    static bool s_userBusy;  // Count is in use
public:
    VNUser4InUse()      { allocate(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    ~VNUser4InUse()     { free    (4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void clear() { clearcnt(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
    static void check() { checkcnt(4, s_userCntGbl/*ref*/, s_userBusy/*ref*/); }
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

    // Delete all previously pushed nodes (by calling deleteTree)
    void doDeletes();

    // Do the deletions on destruction
    ~VNDeleter() { doDeletes(); }
};

//######################################################################
// VNVisitorConst -- Allows new functions to be called on each node
// type without changing the base classes.  See "Modern C++ Design".
// This only has the constant fuctions for non-modifying visitors.
// For more typical usage see VNVisitor

class VNVisitorConst VL_NOT_FINAL {
    friend class AstNode;

public:
    /// Call visit()s on nodep
    inline void iterateConst(AstNode* nodep);
    /// Call visit()s on nodep
    inline void iterateConstNull(AstNode* nodep);
    /// Call visit()s on const nodep's children
    inline void iterateChildrenConst(AstNode* nodep);
    /// Call visit()s on nodep's children in backp() order
    inline void iterateChildrenBackwardsConst(AstNode* nodep);
    /// Call visit()s on const nodep (maybe nullptr) and nodep's nextp() list
    inline void iterateAndNextConstNull(AstNode* nodep);

    virtual void visit(AstNode* nodep) = 0;
    virtual ~VNVisitorConst() {}
#include "V3Ast__gen_visitor_decls.h"  // From ./astgen
};

//######################################################################
// VNVisitor -- Allows new functions to be called on each node
// type without changing the base classes.  See "Modern C++ Design".

class VNVisitor VL_NOT_FINAL : public VNVisitorConst {
    VNDeleter m_deleter;  // Used to delay deletion of nodes
public:
    /// Call visit()s on nodep
    inline void iterate(AstNode* nodep);
    /// Call visit()s on nodep
    inline void iterateNull(AstNode* nodep);
    /// Call visit()s on nodep's children
    inline void iterateChildren(AstNode* nodep);
    /// Call visit()s on nodep (maybe nullptr) and nodep's nextp() list
    inline void iterateAndNextNull(AstNode* nodep);
    /// Return edited nodep; see comments in V3Ast.cpp
    inline AstNode* iterateSubtreeReturnEdits(AstNode* nodep);

    VNDeleter& deleter() { return m_deleter; }
    void pushDeletep(AstNode* nodep) { deleter().pushDeletep(nodep); }
    void doDeletes() { deleter().doDeletes(); }
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
    AstNode** m_iterpp = nullptr;
    RelinkWhatEn m_chg = RELINK_BAD;

public:
    VNRelinker() = default;
    ~VNRelinker() {
        // Relink is needed so m_iterpp's get restored, e.g. can't have:
        // ->unlinkFrBack(relinker);
        // if (only_sometimes) relinker.relink(newp);
        UDEBUGONLY(
            UASSERT_STATIC(!m_backp, "Active linker must be relink()ed before destruction"););
    }
    inline void relink(AstNode* newp);
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
    AstNode* m_headtailp;  // When at begin/end of list, the opposite end of the list, else nullptr
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
    AstNode* cloneTreeIter(bool needPure);
    AstNode* cloneTreeIterList(bool needPure);
    void checkTreeIter(const AstNode* prevBackp) const VL_MT_STABLE;
    bool gateTreeIter() const;
    static bool sameTreeIter(const AstNode* node1p, const AstNode* node2p, bool ignNext,
                             bool gateOnly);
    void deleteTreeIter();
    void deleteNode();
    string instanceStr() const;

public:
    void purityCheck();
    static void relinkOneLink(AstNode*& pointpr, AstNode* newp);
    // cppcheck-suppress functionConst
    static void debugTreeChange(const AstNode* nodep, const char* prefix, int lineno, bool next);

protected:
    // CONSTRUCTORS
    AstNode(VNType t, FileLine* fl);
    virtual ~AstNode() = default;  // Use 'deleteTree' instead
    virtual AstNode* clone() = 0;  // Generally, cloneTree is what you want instead
    virtual void cloneRelink() { cloneRelinkGen(); }
    virtual void cloneRelinkGen() {};  // Overrides generated by 'astgen'
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

    // Use instead isSame(), this is for each Ast* class, and assumes node is of same type
    virtual bool sameNode(const AstNode*) const { return true; }
    // Generated by 'astgen'. If do an oldp->replaceNode(newp), would cause a broken()
    virtual bool wouldBreakGen(const AstNode* const oldp,
                               const AstNode* const newp) const
        = 0;  // Generated by 'astgen'

public:
    // ACCESSORS
    VNType type() const VL_MT_SAFE { return m_type; }
    const char* typeName() const VL_MT_SAFE { return type().ascii(); }  // See also prettyTypeName
    AstNode* nextp() const VL_MT_STABLE { return m_nextp; }
    AstNode* backp() const VL_MT_STABLE { return m_backp; }
    AstNode* abovep() const;  // Get parent node above, only for list head and tail
    AstNode* op1p() const VL_MT_STABLE { return m_op1p; }
    AstNode* op2p() const VL_MT_STABLE { return m_op2p; }
    AstNode* op3p() const VL_MT_STABLE { return m_op3p; }
    AstNode* op4p() const VL_MT_STABLE { return m_op4p; }
    AstNodeDType* dtypep() const VL_MT_STABLE { return m_dtypep; }
    AstNode* clonep() const { return ((m_cloneCnt == s_cloneCntGbl) ? m_clonep : nullptr); }
    AstNode* firstAbovep() const {  // Returns nullptr when second or later in list
        return ((backp() && backp()->nextp() != this) ? backp() : nullptr);
    }
    uint8_t brokenState() const VL_MT_SAFE { return m_brokenState; }
    void brokenState(uint8_t value) { m_brokenState = value; }

    // Used by AstNode::broken()
    bool brokeExists() const { return V3Broken::isLinkable(this); }
    bool brokeExistsAbove() const { return brokeExists() && (m_brokenState >> 7); }

    // Perform a function on every link in a node
    virtual void foreachLink(std::function<void(AstNode** linkpp, const char* namep)> f) = 0;

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
    static constexpr int INSTR_COUNT_SYM = 5;  // Syms ctor/dtor statements

    // ACCESSORS
    virtual string name() const VL_MT_STABLE { return ""; }
    virtual string origName() const { return ""; }
    string prettyDehashOrigOrName() const {
        return prettyName(VName::dehash(origName().empty() ? name() : origName()));
    }
    virtual void name(const string& name) {
        this->v3fatalSrc("name() called on object without name() method");
    }
    virtual void tag(const string& text) {}
    virtual string tag() const { return ""; }
    virtual uint32_t declTokenNum() const { return 0; }
    virtual void declTokenNumSetMin(uint32_t tokenNum) {}
    virtual string verilogKwd() const { return ""; }
    string nameProtect() const VL_MT_STABLE;  // Name with --protect-id applied
    string origNameProtect() const;  // origName with --protect-id applied
    string shortName() const;  // Name with __PVT__ removed for concatenating scopes
    static string dedotName(const string& namein);  // Name with dots removed
    static string prettyName(const string& namein) VL_PURE;  // Name for printing out to the user
    static string vpiName(const string& namein);  // Name for vpi access
    static string prettyNameQ(const string& namein) {  // Quoted pretty name (for errors)
        return "'"s + prettyName(namein) + "'";
    }
    // Encode user name into internal C representation
    static string encodeName(const string& namein);
    static string encodeNumber(int64_t num);  // Encode number into internal C representation
    static string vcdName(const string& namein);  // Name for printing out to vcd files
    string prettyName() const { return prettyName(name()); }
    string prettyNameQ() const { return prettyNameQ(name()); }
    // "VARREF" for error messages (NOT dtype's pretty name)
    string prettyTypeName() const;
    virtual string prettyOperatorName() const { return "operator " + prettyTypeName(); }
    FileLine* fileline() const VL_MT_SAFE { return m_fileline; }
    void fileline(FileLine* fl) { m_fileline = fl; }
    inline bool width1() const;
    inline int widthInstrs() const;
    bool didWidth() const { return m_flags.didWidth; }
    void didWidth(bool flag) { m_flags.didWidth = flag; }
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
    inline int width() const VL_MT_STABLE;
    inline int widthMin() const VL_MT_STABLE;
    int widthMinV() const {
        return v3Global.widthMinUsage() == VWidthMinUsage::VERILOG_WIDTH ? widthMin() : width();
    }
    int widthWords() const { return VL_WORDS_I(width()); }
    bool isQuad() const VL_MT_STABLE { return (width() > VL_IDATASIZE && width() <= VL_QUADSIZE); }
    bool isWide() const VL_MT_STABLE { return (width() > VL_QUADSIZE); }
    inline bool isDouble() const VL_MT_STABLE;
    inline bool isSigned() const VL_MT_STABLE;
    inline bool isString() const VL_MT_STABLE;
    inline bool isEvent() const VL_MT_STABLE;

    // clang-format off
    VNUser user1u() const VL_MT_STABLE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser1InUse::s_userBusy, "user1p used without AstUserInUse");
        return ((m_user1Cnt == VNUser1InUse::s_userCntGbl) ? m_user1u : VNUser{0});
    }
    AstNode* user1p() const VL_MT_STABLE { return user1u().toNodep(); }
    void user1u(const VNUser& user) { m_user1u = user; m_user1Cnt = VNUser1InUse::s_userCntGbl; }
    void user1p(void* userp) { user1u(VNUser{userp}); }
    void user1(int val) { user1u(VNUser{val}); }
    int user1() const { return user1u().toInt(); }
    int user1Inc(int val = 1) { int v = user1(); user1(v + val); return v; }
    int user1SetOnce() { int v = user1(); if (!v) user1(1); return v; }  // Better for cache than user1Inc()
    static void user1ClearTree() { VNUser1InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser user2u() const VL_MT_STABLE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser2InUse::s_userBusy, "user2p used without AstUserInUse");
        return ((m_user2Cnt == VNUser2InUse::s_userCntGbl) ? m_user2u : VNUser{0});
    }
    AstNode* user2p() const VL_MT_STABLE { return user2u().toNodep(); }
    void user2u(const VNUser& user) { m_user2u = user; m_user2Cnt = VNUser2InUse::s_userCntGbl; }
    void user2p(void* userp) { user2u(VNUser{userp}); }
    void user2(int val) { user2u(VNUser{val}); }
    int user2() const { return user2u().toInt(); }
    int user2Inc(int val = 1) { int v = user2(); user2(v + val); return v; }
    int user2SetOnce() { int v = user2(); if (!v) user2(1); return v; }  // Better for cache than user2Inc()
    static void user2ClearTree() { VNUser2InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser user3u() const VL_MT_STABLE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser3InUse::s_userBusy, "user3p used without AstUserInUse");
        return ((m_user3Cnt == VNUser3InUse::s_userCntGbl) ? m_user3u : VNUser{0});
    }
    AstNode* user3p() const VL_MT_STABLE { return user3u().toNodep(); }
    void user3u(const VNUser& user) { m_user3u = user; m_user3Cnt = VNUser3InUse::s_userCntGbl; }
    void user3p(void* userp) { user3u(VNUser{userp}); }
    void user3(int val) { user3u(VNUser{val}); }
    int user3() const { return user3u().toInt(); }
    int user3Inc(int val = 1) { int v = user3(); user3(v + val); return v; }
    int user3SetOnce() { int v = user3(); if (!v) user3(1); return v; }  // Better for cache than user3Inc()
    static void user3ClearTree() { VNUser3InUse::clear(); }  // Clear userp()'s across the entire tree

    VNUser user4u() const VL_MT_STABLE {
        // Slows things down measurably, so disabled by default
        //UASSERT_STATIC(VNUser4InUse::s_userBusy, "user4p used without AstUserInUse");
        return ((m_user4Cnt == VNUser4InUse::s_userCntGbl) ? m_user4u : VNUser{0});
    }
    AstNode* user4p() const VL_MT_STABLE { return user4u().toNodep(); }
    void user4u(const VNUser& user) { m_user4u = user; m_user4Cnt = VNUser4InUse::s_userCntGbl; }
    void user4p(void* userp) { user4u(VNUser{userp}); }
    void user4(int val) { user4u(VNUser{val}); }
    int user4() const { return user4u().toInt(); }
    int user4Inc(int val = 1) { int v = user4(); user4(v + val); return v; }
    int user4SetOnce() { int v = user4(); if (!v) user4(1); return v; }  // Better for cache than user4Inc()
    static void user4ClearTree() { VNUser4InUse::clear(); }  // Clear userp()'s across the entire tree
    // clang-format on

#ifdef VL_DEBUG
    uint64_t editCount() const { return m_editCount; }
    void editCountInc() {
        m_editCount = ++s_editCntGbl;  // Preincrement, so can "watch AstNode::s_editCntGbl=##"
        VIsCached::clearCacheTree();  // Any edit clears all caching
    }
#else
    void editCountInc() { ++s_editCntGbl; }
#endif
    static uint64_t editCountLast() VL_MT_SAFE { return s_editCntLast; }
    static uint64_t editCountGbl() VL_MT_SAFE { return s_editCntGbl; }
    static void editCountSetLast() { s_editCntLast = editCountGbl(); }

    // ACCESSORS for specific types
    // Alas these can't be virtual or they break when passed a nullptr
    inline bool isClassHandleValue() const;
    inline bool isNull() const;
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
    void dtypeSetStream() { dtypep(findStreamDType()); }
    void dtypeSetVoid() { dtypep(findVoidDType()); }

    // Data type locators
    AstNodeDType* findBitDType() const { return findBasicDType(VBasicDTypeKwd::LOGIC); }
    AstNodeDType* findDoubleDType() const { return findBasicDType(VBasicDTypeKwd::DOUBLE); }
    AstNodeDType* findIntDType() const { return findBasicDType(VBasicDTypeKwd::INT); }
    AstNodeDType* findStringDType() const { return findBasicDType(VBasicDTypeKwd::STRING); }
    AstNodeDType* findSigned8DType() const { return findBasicDType(VBasicDTypeKwd::BYTE); }
    AstNodeDType* findSigned32DType() const { return findBasicDType(VBasicDTypeKwd::INTEGER); }
    AstNodeDType* findUInt32DType() const { return findBasicDType(VBasicDTypeKwd::UINT32); }
    AstNodeDType* findUInt64DType() const { return findBasicDType(VBasicDTypeKwd::UINT64); }
    AstNodeDType* findCHandleDType() const { return findBasicDType(VBasicDTypeKwd::CHANDLE); }
    AstNodeDType* findConstraintRefDType() const;
    AstNodeDType* findEmptyQueueDType() const;
    AstNodeDType* findQueueIndexDType() const;
    AstNodeDType* findStreamDType() const;
    AstNodeDType* findVoidDType() const;
    AstNodeDType* findBitDType(int width, int widthMin, VSigning numeric) const;
    AstNodeDType* findLogicDType(int width, int widthMin, VSigning numeric) const;
    AstNodeDType* findLogicRangeDType(const VNumRange& range, int widthMin,
                                      VSigning numeric) const VL_MT_STABLE;
    AstNodeDType* findBitRangeDType(const VNumRange& range, int widthMin,
                                    VSigning numeric) const VL_MT_STABLE;
    AstNodeDType* findBasicDType(VBasicDTypeKwd kwd) const;
    static AstBasicDType* findInsertSameDType(AstBasicDType* nodep);

    static VCastable computeCastable(const AstNodeDType* toDtp, const AstNodeDType* fromDtp,
                                     const AstNode* fromConstp);
    static AstNodeDType* getCommonClassTypep(AstNode* nodep1, AstNode* nodep2);

    // METHODS - dump and error
    void v3errorEnd(const std::ostringstream& str) const VL_RELEASE(V3Error::s().m_mutex);
    void v3errorEndFatal(const std::ostringstream& str) const VL_ATTR_NORETURN
        VL_RELEASE(V3Error::s().m_mutex);
    string warnContextPrimary() const VL_REQUIRES(V3Error::s().m_mutex) {
        return fileline()->warnContextPrimary();
    }
    string warnContextSecondary() const { return fileline()->warnContextSecondary(); }
    string warnMore() const VL_REQUIRES(V3Error::s().m_mutex) { return fileline()->warnMore(); }
    string warnOther() const VL_REQUIRES(V3Error::s().m_mutex) { return fileline()->warnOther(); }

    virtual void dump(std::ostream& str = std::cout) const;
    static char* dumpTreeJsonGdb(const AstNode* nodep);  // For GDB only, free()d by caller
    static char* dumpTreeJsonGdb(const char* str);  // For GDB only, free()d by caller
    static char* dumpTreeJsonGdb(intptr_t nodep);  // For GDB only, free()d by caller
    static void dumpGdb(const AstNode* nodep);  // For GDB only
    void dumpGdbHeader() const;

    // METHODS - Tree modifications
    // Returns nodep. If newp is not nullptr, then add it to end of nodep's list.
    template <typename T_NodeResult, typename T_NodeNext>
    static T_NodeResult* addNext(T_NodeResult* nodep, T_NodeNext* newp) {
        static_assert(std::is_base_of<AstNode, T_NodeResult>::value,
                      "'T_NodeResult' must be a subtype of AstNode");
        static_assert(std::is_base_of<T_NodeResult, T_NodeNext>::value,
                      "'T_NodeNext' must be a subtype of 'T_NodeResult'");
        if (!newp) return nodep;
        return static_cast<T_NodeResult*>(addNext<AstNode, AstNode>(nodep, newp));
    }
    inline AstNode* addNext(AstNode* newp);
    void addNextHere(AstNode* newp);  // Insert newp at this->nextp
    void addHereThisAsNext(AstNode* newp);  // Adds at old place of this, this becomes next
    void replaceWith(AstNode* newp);  // Replace current node in tree with new node
    void replaceWithKeepDType(AstNode* newp);  // Replace current node in tree, keep old dtype
    // Unlink this from whoever points to it.
    AstNode* unlinkFrBack(VNRelinker* linkerp = nullptr);
    // Unlink this from whoever points to it, keep entire next list with unlinked node
    AstNode* unlinkFrBackWithNext(VNRelinker* linkerp = nullptr);
    void relink(VNRelinker* linkerp);  // Generally use linker->relink() instead
    void cloneRelinkNode() { cloneRelink(); }

    // METHODS - Iterate on a tree
    AstNode* cloneTree(bool cloneNextLink,
                       bool needPure = false);  // Not const, as sets clonep() on original nodep
    AstNode* cloneTreePure(bool cloneNextLink) { return cloneTree(cloneNextLink, true); }
    bool gateTree() { return gateTreeIter(); }  // Is tree isGateOptimizable?
    inline bool sameTree(const AstNode* node2p) const;  // Does tree of this == node2p?
    // Does tree of this == node2p?, not allowing non-isGateOptimizable
    inline bool sameGateTree(const AstNode* node2p) const;
    void deleteTree();  // Always deletes the next link
    void checkTree() const VL_MT_STABLE {
        if (v3Global.opt.debugCheck()) checkTreeIter(backp());
    }
    void checkIter() const;
    void dumpPtrs(std::ostream& os = std::cout) const;
    void dumpTree(std::ostream& os = std::cout, const string& indent = "    ",
                  int maxDepth = 0) const;
    void dumpTree(const string& indent, int maxDepth = 0) const {
        dumpTree(std::cout, indent, maxDepth);
    }
    static void dumpTreeGdb(const AstNode* nodep);  // For GDB only
    void dumpTreeAndNext(std::ostream& os = std::cout, const string& indent = "    ",
                         int maxDepth = 0) const;
    void dumpTreeFile(const string& filename, bool doDump = true);
    static void dumpTreeFileGdb(const AstNode* nodep, const char* filenamep = nullptr);
    void dumpTreeDot(std::ostream& os = std::cout) const;
    void dumpTreeDotFile(const string& filename, bool doDump = true);
    virtual void dumpJson(std::ostream& os) const { dumpJsonGen(os); };  // node-specific fields
    // Generated by 'astgen'. Dumps node-specific pointers and calls 'dumpJson()' of parent class
    // Note that we don't make it virtual as it would result in infinite recursion
    void dumpJsonGen(std::ostream& os) const {};
    virtual void dumpTreeJsonOpGen(std::ostream& os, const string& indent) const {};
    void dumpTreeJson(std::ostream& os, const string& indent = "") const;
    void dumpTreeJsonFile(const string& filename, bool doDump = true);
    static void dumpJsonMetaFileGdb(const char* filename);
    static void dumpJsonMetaFile(const string& filename);

    // Render node address for dumps. By default this is just the address
    // printed as hex, but with --dump-tree-addrids we map addresses to short
    // strings with a bijection to aid human readability. Observe that this might
    // not actually be a unique identifier as the address can get reused after a
    // node has been freed.
    static std::string nodeAddr(const AstNode* nodep) {
        return v3Global.opt.dumpTreeAddrids() ? v3Global.ptrToId(nodep) : cvtToHex(nodep);
    }

    // METHODS - static advancement
    static AstNode* afterCommentp(AstNode* nodep) {
        // Skip over comments starting at provided nodep,
        // such as to determine if a AstIf is empty.
        // nodep may be null, if so return nullptr.
        while (nodep && VN_IS(nodep, Comment)) nodep = nodep->nextp();
        return nodep;
    }

    // METHODS - queries
    // Changes control flow, disable some optimizations
    virtual bool isBrancher() const { return false; }
    // Else a AstTime etc that can't be pushed out
    virtual bool isGateOptimizable() const { return !isTimingControl(); }
    // GateDedupable is a slightly larger superset of GateOptimzable (eg, AstNodeIf)
    virtual bool isGateDedupable() const { return isGateOptimizable(); }
    // Whether the node can be used in expression coverage
    virtual bool isExprCoverageEligible() const { return isGateDedupable(); }
    // Else creates output or exits, etc, not unconsumed
    virtual bool isOutputter() { return false; }
    // Else a AstTime etc which output can't be predicted from input
    virtual bool isPredictOptimizable() const { return !isTimingControl(); }
    // Else a $display, etc, that must be ordered with other displays
    virtual bool isPure() { return true; }
    // Iff isPure on current node and any nextp()
    bool isPureAndNext() { return isPure() && (!nextp() || nextp()->isPure()); }
    // An event control, delay, wait, etc.
    virtual bool isTimingControl() const { return false; }
    // isUnlikely handles $stop or similar statement which means an above IF
    // statement is unlikely to be taken
    virtual bool isUnlikely() const { return false; }
    // Is an IEEE system function (versus internally-generated)
    virtual bool isSystemFunc() const { return false; }
    virtual int instrCount() const { return 0; }
    // Iff node is identical to another node
    virtual bool isSame(const AstNode* samep) const {
        return type() == samep->type() && sameNode(samep);
    }
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
    // Generated by 'astgen'. Calls 'broken()', which can be used to add extra checks
    virtual const char* brokenGen() const = 0;  // Generated by 'astgen'
    // If do a this->replaceNode(newp), would cause a broken()
    bool wouldBreak(const AstNode* const newp) const { return backp()->wouldBreakGen(this, newp); }

    // INVOKERS
    virtual void accept(VNVisitorConst& v) = 0;

protected:
    // All VNVisitor related functions are called as methods off the visitor
    friend class VNVisitor;
    friend class VNVisitorConst;
    // Use instead VNVisitor::iterateChildren
    void iterateChildren(VNVisitor& v);
    // Use instead VNVisitor::iterateChildrenBackwardsConst
    void iterateChildrenBackwardsConst(VNVisitorConst& v);
    // Use instead VNVisitor::iterateChildrenConst
    void iterateChildrenConst(VNVisitorConst& v);
    // Use instead VNVisitor::iterateAndNextNull
    void iterateAndNext(VNVisitor& v);
    // Use instead VNVisitor::iterateAndNextConstNull
    void iterateAndNextConst(VNVisitorConst& v);
    // Use instead VNVisitor::iterateSubtreeReturnEdits
    AstNode* iterateSubtreeReturnEdits(VNVisitor& v);

    static void dumpJsonNum(std::ostream& os, const std::string& name, int64_t val);
    static void dumpJsonBool(std::ostream& os, const std::string& name, bool val);
    static void dumpJsonBoolIf(std::ostream& os, const std::string& name, bool val);
    static void dumpJsonStr(std::ostream& os, const std::string& name, const std::string& val);
    static void dumpJsonPtr(std::ostream& os, const std::string& name, const AstNode* const valp);

protected:
    void iterateListBackwardsConst(VNVisitorConst& v);

    // For internal use only.
    // Note: specializations for particular node types are provided by 'astgen'
    template <typename T>
    inline static bool privateTypeTest(const AstNode* nodep);

    // For internal use only.
    template <typename T_TargetType, typename T_DeclType>
    constexpr static bool uselessCast() VL_PURE {  // LCOV_EXCL_START
        using NonRef = typename std::remove_reference<T_DeclType>::type;
        using NonPtr = typename std::remove_pointer<NonRef>::type;
        using NonCV = typename std::remove_cv<NonPtr>::type;
        return std::is_base_of<T_TargetType, NonCV>::value;
    }  // LCOV_EXCL_STOP

    // For internal use only.
    template <typename T_TargetType, typename T_DeclType>
    constexpr static bool impossibleCast() VL_PURE {  // LCOV_EXCL_START
        using NonRef = typename std::remove_reference<T_DeclType>::type;
        using NonPtr = typename std::remove_pointer<NonRef>::type;
        using NonCV = typename std::remove_cv<NonPtr>::type;
        return !std::is_base_of<NonCV, T_TargetType>::value;
    }  // LCOV_EXCL_STOP

public:
    // For use via the VN_IS macro only, or in templated code
    template <typename T_TargetType, typename T_Node>
    static bool is(const T_Node* nodep) VL_MT_SAFE {
        static_assert(std::is_base_of<AstNode, T_Node>::value, "VN_IS called on non AstNode");
        static_assert(!uselessCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_IS, node known to have target type.");
        static_assert(!impossibleCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_IS, node cannot be this type.");
        return nodep && privateTypeTest<T_TargetType>(nodep);
    }

    // For use via the VN_CAST macro only, or in templated code
    template <typename T_TargetType, typename T_Node>
    static T_TargetType* cast(T_Node* nodep) VL_MT_SAFE {
        static_assert(std::is_base_of<AstNode, T_Node>::value, "VN_CAST called on non AstNode");
        static_assert(!uselessCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_CAST, node known to have target type.");
        static_assert(!impossibleCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_CAST, node cannot be this type.");
        return nodep && privateTypeTest<T_TargetType>(nodep)
                   ? reinterpret_cast<T_TargetType*>(nodep)
                   : nullptr;
    }
    template <typename T_TargetType, typename T_Node>
    static const T_TargetType* cast(const T_Node* nodep) VL_MT_SAFE {
        static_assert(std::is_base_of<AstNode, T_Node>::value, "VN_CAST called on non AstNode");
        static_assert(!uselessCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_CAST, node known to have target type.");
        static_assert(!impossibleCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_CAST, node cannot be this type.");
        return nodep && privateTypeTest<T_TargetType>(nodep)
                   ? reinterpret_cast<const T_TargetType*>(nodep)
                   : nullptr;
    }

    // For use via the VN_AS macro only, or in templated code
    template <typename T_TargetType, typename T_Node>
    static T_TargetType* as(T_Node* nodep) VL_PURE {
        static_assert(std::is_base_of<AstNode, T_Node>::value, "VN_AS called on non AstNode");
        static_assert(!uselessCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_AS, node known to have target type.");
        static_assert(!impossibleCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_AS, node cannot be this type.");
        UASSERT_OBJ(!nodep || privateTypeTest<T_TargetType>(nodep), nodep,
                    "AstNode is not of expected type, but instead has type '" << nodep->typeName()
                                                                              << "'");
        return unsafePrivateAs<T_TargetType, T_Node>(nodep);
    }
    template <typename T_TargetType, typename T_Node>
    static const T_TargetType* as(const T_Node* nodep) VL_PURE {
        static_assert(std::is_base_of<AstNode, T_Node>::value, "VN_AS called on non AstNode");
        static_assert(!uselessCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_AS, node known to have target type.");
        static_assert(!impossibleCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_AS, node cannot be this type.");
        UASSERT_OBJ(!nodep || privateTypeTest<T_TargetType>(nodep), nodep,
                    "AstNode is not of expected type, but instead has type '" << nodep->typeName()
                                                                              << "'");
        return unsafePrivateAs<T_TargetType, T_Node>(nodep);
    }

    // For use via privateAs or the VN_DBG_AS macro only
    template <typename T_TargetType, typename T_Node>
    static T_TargetType* unsafePrivateAs(T_Node* nodep) VL_PURE {
        static_assert(std::is_base_of<AstNode, T_Node>::value, "VN_DBG_AS called on non AstNode");
        static_assert(!uselessCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_DBG_AS, node known to have target type.");
        static_assert(!impossibleCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_DBG_AS, node cannot be this type.");
        return reinterpret_cast<T_TargetType*>(nodep);
    }
    template <typename T_TargetType, typename T_Node>
    static const T_TargetType* unsafePrivateAs(const T_Node* nodep) VL_PURE {
        static_assert(std::is_base_of<AstNode, T_Node>::value, "VN_DBG_AS called on non AstNode");
        static_assert(!uselessCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_DBG_AS, node known to have target type.");
        static_assert(!impossibleCast<T_TargetType, T_Node>(),
                      "Unnecessary VN_DBG_AS, node cannot be this type.");
        return reinterpret_cast<const T_TargetType*>(nodep);
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

    template <typename T_Arg, typename T_Callable>
    inline static void foreachImpl(ConstCorrectAstNode<T_Arg>* nodep, const T_Callable& f,
                                   bool visitNext);

    template <typename T_Arg, bool N_Default, typename T_Callable>
    inline static bool predicateImpl(ConstCorrectAstNode<T_Arg>* nodep, const T_Callable& p,
                                     bool visitNext);

public:
    // Given a callable 'f' that takes a single argument of some AstNode subtype 'T_Node', traverse
    // the tree rooted at this node, and call 'f' in pre-order on each node that is of type
    // 'T_Node'. The node passed to the callable 'f' can be removed or replaced, but other editing
    // of the iterated tree is not safe. Prefer 'foreach' over simple VNVisitor that only needs to
    // handle a single (or a few) node types, as it's easier to write, but more importantly, the
    // dispatch to the callable in 'foreach' should be completely predictable by branch target
    // caches in modern CPUs, while it is basically unpredictable for VNVisitor.
    template <typename T_Callable>
    void foreach(T_Callable&& f) {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(vlstd::is_invocable<T_Callable, T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "T_Callable 'f' must have a signature compatible with 'void(T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        foreachImpl<T_Node>(this, f, /* visitNext: */ false);
    }
    // Same as above, but for 'const' nodes
    template <typename T_Callable>
    void foreach(T_Callable&& f) const {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(
            vlstd::is_invocable<T_Callable, const T_Node*>::value
                && std::is_base_of<AstNode, T_Node>::value,
            "T_Callable 'f' must have a signature compatible with 'void(const T_Node*)', "
            "with 'T_Node' being a subtype of 'AstNode'");
        foreachImpl<const T_Node>(this, f, /* visitNext: */ false);
    }
    // Same as 'foreach' but also traverses 'this->nextp()' transitively
    template <typename T_Callable>
    void foreachAndNext(T_Callable&& f) {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(vlstd::is_invocable<T_Callable, T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "T_Callable 'f' must have a signature compatible with 'void(T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        foreachImpl<T_Node>(this, f, /* visitNext: */ true);
    }
    // Same as above, but for 'const' nodes
    template <typename T_Callable>
    void foreachAndNext(T_Callable&& f) const {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(
            vlstd::is_invocable<T_Callable, const T_Node*>::value
                && std::is_base_of<AstNode, T_Node>::value,
            "T_Callable 'f' must have a signature compatible with 'void(const T_Node*)', "
            "with 'T_Node' being a subtype of 'AstNode'");
        foreachImpl<const T_Node>(this, f, /* visitNext: */ true);
    }

    // Given a predicate 'p' that takes a single argument of some AstNode subtype 'T_Node', return
    // true if and only if there exists a node of type 'T_Node' in the tree rooted at this node,
    // that satisfies the predicate 'p'. Returns false if no node of type 'T_Node' is present.
    // Traversal is performed in some arbitrary order and is terminated as soon as the result can
    // be determined.
    template <typename T_Callable>
    bool exists(T_Callable&& p) {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(vlstd::is_invocable_r<bool, T_Callable, T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<T_Node, /* N_Default: */ false>(this, p, /* visitNext: */ false);
    }
    // Same as above, but for 'const' nodes
    template <typename T_Callable>
    bool exists(T_Callable&& p) const {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(vlstd::is_invocable_r<bool, T_Callable, const T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(const T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<const T_Node, /* N_Default: */ false>(this, p,
                                                                   /* visitNext: */ false);
    }
    // Same as 'exists' but also traverses 'this->nextp()' transitively
    template <typename T_Callable>
    bool existsAndNext(T_Callable&& p) {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(vlstd::is_invocable_r<bool, T_Callable, const T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(const T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<T_Node, /* N_Default: */ false>(this, p, /* visitNext: */ true);
    }
    // Same as above, but for 'const' nodes
    template <typename T_Callable>
    bool existsAndNext(T_Callable&& p) const {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(vlstd::is_invocable_r<bool, T_Callable, const T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(const T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<const T_Node, /* N_Default: */ false>(this, p, /* visitNext: */ true);
    }

    // Given a predicate 'p' that takes a single argument of some AstNode subtype 'T_Node', return
    // true if and only if all nodes of type 'T_Node' in the tree rooted at this node satisfy the
    // predicate 'p'. Returns true if no node of type 'T_Node' is present. Traversal is performed
    // in some arbitrary order and is terminated as soon as the result can be determined.
    template <typename T_Callable>
    bool forall(T_Callable&& p) {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(vlstd::is_invocable_r<bool, T_Callable, T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<T_Node, /* N_Default: */ true>(this, p, /* visitNext: */ false);
    }
    // Same as above, but for 'const' nodes
    template <typename T_Callable>
    bool forall(T_Callable&& p) const {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 0>::type;
        static_assert(vlstd::is_invocable_r<bool, T_Callable, const T_Node*>::value
                          && std::is_base_of<AstNode, T_Node>::value,
                      "Predicate 'p' must have a signature compatible with 'bool(const T_Node*)', "
                      "with 'T_Node' being a subtype of 'AstNode'");
        return predicateImpl<const T_Node, /* N_Default: */ true>(this, p, /* visitNext: */ false);
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

// Specializations of privateTypeTest
#include "V3Ast__gen_type_tests.h"  // From ./astgen

// Specializations of AstNode::mayBeUnder
template <>
inline bool AstNode::mayBeUnder<AstCell>(const AstNode* nodep) {
    return !VN_IS(nodep, NodeStmt) && !VN_IS(nodep, NodeExpr);
}
template <>
inline bool AstNode::mayBeUnder<AstNodeAssign>(const AstNode* nodep) {
    return !VN_IS(nodep, NodeExpr);
}
template <>
inline bool AstNode::mayBeUnder<AstVarScope>(const AstNode* nodep) {
    if (VN_IS(nodep, VarScope)) return false;  // Should not nest
    if (VN_IS(nodep, Var)) return false;
    if (VN_IS(nodep, Active)) return false;
    if (VN_IS(nodep, NodeStmt)) return false;
    if (VN_IS(nodep, NodeExpr)) return false;
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
template <typename T_Arg, typename T_Callable>
void AstNode::foreachImpl(ConstCorrectAstNode<T_Arg>* nodep, const T_Callable& f, bool visitNext) {
    // Pre-order traversal implemented directly (without recursion) for speed reasons. The very
    // first iteration (the one that operates on the input nodep) is special, as we might or
    // might not need to enqueue nodep->nextp() depending on VisitNext, while in all other
    // iterations, we do want to enqueue nodep->nextp(). Duplicating code (via
    // 'foreachImplVisit') for the initial iteration here to avoid an extra branch in the loop

    using T_Arg_NonConst = typename std::remove_const<T_Arg>::type;
    using Node = ConstCorrectAstNode<T_Arg>;

    // We prefetch this far into the stack
    constexpr int PrefetchDistance = 2;
    // We push max 5 items per iteration
    constexpr size_t MaxPushesPerIteration = 5;
    // Initial stack sie
    constexpr size_t InitialStackSize = 32;

    // Traversal stack. Because we often iterate over small trees, use an in-line initial stack
    size_t stackSize = InitialStackSize;
    Node* inLineStack[InitialStackSize];  // In-line initial stack storage
    std::unique_ptr<Node*[]> outOfLineStackp{nullptr};  // In case we need more, we will allocate
    Node** basep = inLineStack + PrefetchDistance;  // Pointer to base of stack
    Node** topp = basep;  // Pointer to top of stack
    Node** limp = inLineStack + stackSize - MaxPushesPerIteration;  // Pointer to grow limit

    // We want some non-null pointers at the beginning. These will be prefetched, but not
    // visited, so the root node will suffice. This eliminates needing branches in the loop.
    for (int i = -PrefetchDistance; i; ++i) basep[i] = nodep;

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
        ASTNODE_PREFETCH_NON_NULL(topp[-PrefetchDistance]);

        // Ensure we have stack space for nextp and the 4 children
        if (VL_UNLIKELY(topp >= limp)) {
            const ptrdiff_t occupancy = topp - basep;
            {
                const size_t newStackSize = stackSize * 2;
                Node** const newStackp = new Node*[newStackSize];
                std::memcpy(newStackp, basep - PrefetchDistance,
                            sizeof(Node**) * (occupancy + PrefetchDistance));
                stackSize = newStackSize;
                outOfLineStackp.reset(newStackp);
            }
            basep = outOfLineStackp.get() + PrefetchDistance;
            topp = basep + occupancy;
            limp = outOfLineStackp.get() + stackSize - MaxPushesPerIteration;
        }

        // Enqueue the next node
        if (headp->nextp()) *topp++ = headp->nextp();

        // Visit the head node
        visit(headp);
    }
}

// predicate implementation
template <typename T_Arg, bool N_Default, typename T_Callable>
bool AstNode::predicateImpl(ConstCorrectAstNode<T_Arg>* nodep, const T_Callable& p,
                            bool visitNext) {
    // Implementation similar to foreach, but abort traversal as soon as result is determined
    using T_Arg_NonConst = typename std::remove_const<T_Arg>::type;
    using Node = ConstCorrectAstNode<T_Arg>;

    // We prefetch this far into the stack
    constexpr int PrefetchDistance = 2;
    // We push max 5 items per iteration
    constexpr size_t MaxPushesPerIteration = 5;
    // Initial stack sie
    constexpr size_t InitialStackSize = 32;

    // Traversal stack. Because we often iterate over small trees, use an in-line initial stack
    size_t stackSize = InitialStackSize;
    Node* inLineStack[InitialStackSize];  // In-line initial stack storage
    std::unique_ptr<Node*[]> outOfLineStackp{nullptr};  // In case we need more, we will allocate
    Node** basep = inLineStack + PrefetchDistance;  // Pointer to base of stack
    Node** topp = basep;  // Pointer to top of stack
    Node** limp = inLineStack + stackSize - MaxPushesPerIteration;  // Pointer to grow limit

    // We want some non-null pointers at the beginning. These will be prefetched, but not
    // visited, so the root node will suffice. This eliminates needing branches in the loop.
    for (int i = -PrefetchDistance; i; ++i) basep[i] = nodep;

    // Visit given node, enqueue children for traversal, return true if result determined.
    const auto visit = [&](Node* currp) {
        // Type test this node
        if (AstNode::privateTypeTest<T_Arg_NonConst>(currp)) {
            // Call the client function
            if (p(static_cast<T_Arg*>(currp)) != N_Default) return true;
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

    // Enqueue the next of the root node, if required
    if (visitNext && nodep->nextp()) *topp++ = nodep->nextp();

    // Visit the root node
    if (visit(nodep)) return !N_Default;

    // Visit the rest of the tree
    while (VL_LIKELY(topp > basep)) {
        // Pop next node in the traversal
        Node* const headp = *--topp;

        // Prefetch in case we are ascending the tree
        ASTNODE_PREFETCH_NON_NULL(topp[-PrefetchDistance]);

        // Ensure we have stack space for nextp and the 4 children
        if (VL_UNLIKELY(topp >= limp)) {
            const ptrdiff_t occupancy = topp - basep;
            {
                const size_t newStackSize = stackSize * 2;
                Node** const newStackp = new Node*[newStackSize];
                std::memcpy(newStackp, basep - PrefetchDistance,
                            sizeof(Node**) * (occupancy + PrefetchDistance));
                stackSize = newStackSize;
                outOfLineStackp.reset(newStackp);
            }
            basep = outOfLineStackp.get() + PrefetchDistance;
            topp = basep + occupancy;
            limp = outOfLineStackp.get() + stackSize - MaxPushesPerIteration;
        }

        // Enqueue the next node
        if (headp->nextp()) *topp++ = headp->nextp();

        // Visit the head node
        if (visit(headp)) return !N_Default;
    }

    return N_Default;
}

inline std::ostream& operator<<(std::ostream& os, const AstNode* rhs) {
    if (!rhs) {  // LCOV_EXCL_LINE
        os << "nullptr";  // LCOV_EXCL_LINE
    } else if (VN_DELETED(rhs)) {  // LCOV_EXCL_LINE
        os << "%E-0x1/deleted!";  // LCOV_EXCL_LINE
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
    // cppcheck-suppress noExplicitConstructor
    VNRef(U&& x)
        : std::reference_wrapper<T_Node>{x} {}
    // cppcheck-suppress noExplicitConstructor
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

void VNVisitorConst::iterateConst(AstNode* nodep) { nodep->accept(*this); }
void VNVisitorConst::iterateConstNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->accept(*this);
}
void VNVisitorConst::iterateChildrenConst(AstNode* nodep) { nodep->iterateChildrenConst(*this); }
void VNVisitorConst::iterateChildrenBackwardsConst(AstNode* nodep) {
    nodep->iterateChildrenBackwardsConst(*this);
}
void VNVisitorConst::iterateAndNextConstNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->iterateAndNextConst(*this);
}

void VNVisitor::iterate(AstNode* nodep) { nodep->accept(*this); }
void VNVisitor::iterateNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->accept(*this);
}
void VNVisitor::iterateChildren(AstNode* nodep) { nodep->iterateChildren(*this); }
void VNVisitor::iterateAndNextNull(AstNode* nodep) {
    if (VL_LIKELY(nodep)) nodep->iterateAndNext(*this);
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

// AstNode subclasses - dependency order matters, so fmt off
// clang-format off
#include "V3AstNodeDType.h"
#include "V3AstNodeOther.h"
#include "V3AstNodeExpr.h"
#include "V3AstNodeStmt.h"
// clang-format on

// Inline function definitions need to go last
#include "V3AstInlines.h"
void dumpNodeListJson(std::ostream& os, const AstNode* nodep, const std::string& listName,
                      const string& indent);

#endif  // Guard
