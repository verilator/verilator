#ifndef VERILATOR_PUREGUARD_H_
#define VERILATOR_PUREGUARD_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3AstNodeExpr.h"
#include "V3AstNodeOther.h"

// Set of all nodes of given types
template <class T, class... tail>
class AstNodeTypeSet VL_NOT_FINAL {
public:
    static bool contains(AstNode* nodep) {
        if (AstNode::privateIs<T, decltype(nodep)>(nodep)) return true;
        return AstNodeTypeSet<tail...>::contains(nodep);
    };
};

template <class T>
class AstNodeTypeSet<T> VL_NOT_FINAL {
public:
    static bool contains(AstNode* nodep) {
        if (AstNode::privateIs<T, decltype(nodep)>(nodep)) return true;
        return false;
    };
};

// Set of all ASTs containg nodes of any types listed
template <class... types>
class AstTreeWithTypeSet VL_NOT_FINAL : VNVisitor {
private:
    bool _found;

    AstTreeWithTypeSet()
        : _found(false) {}
    void visit(AstNode* nodep) override {
        if (AstNodeTypeSet<types...>::contains(nodep)) {
            _found = true;
            return;
        }

        iterateChildren(nodep);
    }

    bool found() { return _found; }

public:
    static bool contains(AstNode* nodep) {
        auto set = AstTreeWithTypeSet<types...>();
        set.iterate(nodep);
        return set.found();
    }
};

// Set of all ASTs which may possibly introduce side-effects
using MutatorAstSet
    = AstTreeWithTypeSet<AstAssign, AstTaskRef, /* Remove when we support checking tasks */
                         AstFuncRef, /* Remove when we support checking functions */
                         AstMethodCall, /* Remove when we support checking methods */
                         AstPostAdd, AstPostSub, AstPreAdd, AstPreSub, AstDisplay, AstNew,
                         AstNewCopy>;

#endif /* VERILATOR_PUREGUARD_H_ */
