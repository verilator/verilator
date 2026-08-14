---
name: verilator-examples
description: Complete worked examples for common Verilator development tasks: new pass, new warning, new AST node, bug fix, feature
---

# Verilator Worked Examples Skill

## Example 1: Adding a New Compiler Pass

### Scenario
Add a pass that detects and warns about unreachable code after `return` in functions.

**Reference PR:** #8061 (NFA lazy invalidation), #8101 (Optimize NFA ring buffer)

### Step 1: Create the Pass File
```cpp
// src/V3Unreachable.cpp
// DESCRIPTION: Verilator: Detect unreachable statements after return/break/continue
//
// This pass walks function/task bodies and marks statements that cannot be
// reached due to unconditional control flow (return, break, continue).
// It emits UNREACHABLE warning for each unreachable statement.

#include "V3Unreachable.h"
#include "V3Ast.h"
#include "V3Error.h"

namespace V3Unreachable {

class UnreachableVisitor : public VNVisitor {
    // Tracks whether we're in unreachable code
    bool m_unreachable = false;
    VL_RESTORER(m_unreachable);

    // Current function/task for context in warnings
    AstNodeFTask* m_currentFTaskp = nullptr;
    VL_RESTORER(m_currentFTaskp);

public:
    static void apply(AstNetlist* nodep) {
        UnreachableVisitor().iterate(nodep);
    }

    void visit(AstNodeFTask* nodep) {
        m_currentFTaskp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstReturn* nodep) {
        m_unreachable = true;
        iterateChildren(nodep);
    }

    void visit(AstBreak* nodep) {
        if (nodep->isUnconditional()) m_unreachable = true;
        iterateChildren(nodep);
    }

    void visit(AstContinue* nodep) {
        if (nodep->isUnconditional()) m_unreachable = true;
        iterateChildren(nodep);
    }

    void visit(AstNodeStmt* nodep) {
        if (m_unreachable && !nodep->isCompilerGenerated()) {
            nodep->v3warn(UNREACHABLE,
                "Statement unreachable after unconditional control flow in "
                << m_currentFTaskp->prettyNameQ());
        }
        iterateChildren(nodep);
    }
};

}  // namespace V3Unreachable
```

### Step 2: Create Header
```cpp
// src/V3Unreachable.h
#ifndef V3Unreachable_H
#define V3Unreachable_H

#include "VNVisitor.h"

class AstNetlist;

namespace V3Unreachable {
    void apply(AstNetlist* nodep);
}

#endif
```

### Step 3: Register in Verilator.cpp Pass Pipeline
```cpp
// src/Verilator.cpp - in process() function, after V3Const pass
#include "V3Unreachable.h"
...
V3Unreachable::apply(netlistp);
```

### Step 4: Add Warning Code
```cpp
// src/V3Error.cpp - in V3Error::warnInit()
warnAdd("UNREACHABLE", WARN_DEFAULT_ON,
    "Unreachable code after return/break/continue");
```

### Step 5: Update Warning Documentation
```rst
# docs/guide/warnings.rst
.. _warn-UNREACHABLE:

UNREACHABLE
-----------

Unreachable code after return/break/continue.
```

### Step 6: Create Test
```systemverilog
// test_regress/t/t_lint_unreachable_bad.v
module t;
    function automatic int foo();
        return 1;
        int x = 2;  // UNREACHABLE
    endfunction
    
    task automatic bar();
        return;
        $display("unreachable");  // UNREACHABLE
    endtask
endmodule
```

```python
# test_regress/t/t_lint_unreachable_bad.py
import vltest_bootstrap
test.lint(v_flags=["--lint-only"])
test.passes()
```

```bash
# Generate golden
HARNESS_UPDATE_GOLDEN=1 python3 test_regress/t/t_lint_unreachable_bad.py
```

---

## Example 2: Adding a New AST Node (Illustrative - abridged)

### Scenario
Add `AstAssertFinal` for `assert final` property (SystemVerilog 2023).

**Reference PR:** #7992 (SIMILARNAME warning), #7968 (MULTIDRIVENPROC warning) - shows pattern of warning + AST + test

### Step 1: Declare in V3AstNodeOther.h
```cpp
// In V3AstNodeOther.h - near other assertion nodes
class AstAssertFinal : public AstNodeStmt {
    // @astgen op1 := propertyp : AstNodeExpr        // Property expression
    // @astgen op2 := passActionsp : AstNodeStmt     // Pass action statements
    // @astgen op3 := failActionsp : AstNodeStmt     // Fail action statements
    // @astgen ptr := m_scopep : AstScope            // Scope for this assert
    
    // Required overrides for new AST members
    void dump() const override;
    void dumpJson() const override;
    bool isSame(const AstNode* nodep) const override;
    AstNode* cloneRelink(AstClone& clone) const override;
};
```

### Step 2: Implement in V3Ast.cpp
```cpp
void AstAssertFinal::dump() const {
    dumpHeader("AssertFinal");
    dumpChild(propertyp(), "property");
    if (passActionsp()) dumpChild(passActionsp(), "pass");
    if (failActionsp()) dumpChild(failActionsp(), "fail");
}

void AstAssertFinal::dumpJson() const {
    jsonHeader("AssertFinal");
    jsonChild("property", propertyp());
    if (passActionsp()) jsonChild("pass", passActionsp());
    if (failActionsp()) jsonChild("fail", failActionsp());
    jsonFooter();
}

bool AstAssertFinal::isSame(const AstNode* nodep) const {
    const AstAssertFinal* const other = VN_AS(nodep, AssertFinal);
    return AstNode::isSame(nodep)
        && propertyp()->isSame(other->propertyp())
        && (passActionsp() ? passActionsp()->isSame(other->passActionsp()) : !other->passActionsp())
        && (failActionsp() ? failActionsp()->isSame(other->failActionsp()) : !other->failActionsp());
}

AstNode* AstAssertFinal::cloneRelink(AstClone& clone) const {
    AstAssertFinal* const newp = new AstAssertFinal{fileline()};
    newp->setupPropertyp(clone.relink(propertyp()));
    if (passActionsp()) newp->setupPassActionsp(clone.relink(passActionsp()));
    if (failActionsp()) newp->setupFailActionsp(clone.relink(failActionsp()));
    return newp;
}
```

### Step 3: Add Parser Support (verilog.y)
```yacc
// In assertion_item rule
| K_ASSERT_FINAL property_spec action_block_opt
    { $$ = new AstAssertFinal{@$, $2, $3, nullptr}; }
```

### Step 4: Add Pass Handling
```cpp
// In V3AssertPre.cpp - visit AstAssertFinal
void visit(AstAssertFinal* nodep) {
    // Link property, validate, attach to scheduling
    iterateChildren(nodep);
}

// In V3Sched.cpp - schedule the final assertion
void visit(AstAssertFinal* nodep) {
    // Schedule for final simulation phase
    iterateChildren(nodep);
}
```

### Step 5: Add Test
```systemverilog
// test_regress/t/t_assert_final.v
module t;
    bit clk;
    always #5 clk = ~clk;
    
    assert final (q == 0) else $error("Final check failed");
    
    initial begin
        #100 $finish;
    end
endmodule
```

---

## Example 3: Fixing a Bug (Use-After-Free)

### Scenario
PR #8076: Fix use-after-free of captured interface typedef reference during parameter cloning.

**Reference PRs:** #8094 (Fix hierarchical class scope resolution), #8085 (Fix forceable unpacked array), #8080 (Fix undefined symbol solver error)

### Root Cause Analysis
```cpp
// Problem: During module cloning, interface typedef references were
// being tracked in a global ledger but not properly cleaned up
// when the original module was deleted.

// The ledger tracked ALL nodes, including leaf expressions that
// never needed tracking.
```

### Fix Pattern
```cpp
// src/V3Dead.cpp - in DeadVisitor::cleanup()
void DeadVisitor::cleanup() {
    // Before: tracked everything
    // nodep->foreach([&](AstNode* np) { deadps.insert(np); });
    
    // After: only track nodes that can be in ledger (maybePointedTo)
    nodep->foreach([&](AstNode* np) {
        if (np->maybePointedTo()) deadps.insert(np);
    });
}
```

### Test Case
```systemverilog
// test_regress/t/t_param_clone_iface_typedef_bad.v
package pkg;
    typedef struct { int x; } s_t;
endpackage

module child(input pkg::s_t ifc);
endmodule

module parent;
    pkg::s_t val;
    child #(.ifc(val)) c();
endmodule
```

---

## Example 4: Adding a New Warning (SIMILARNAME)

### Scenario
PR #8020: Warn when variables differ only in lexical case.

**Reference PR:** #7992 (Add SIMILARNAME warning), #7968 (Add MULTIDRIVENPROC warning), #8020 (Implementation)

### Implementation
```cpp
// src/V3LinkDot.cpp - in LinkDotVisitor::visit(AstVar*)
if (varp->isSigPublic()) {
    std::string lower = varp->name();
    for (auto& c : lower) c = tolower(c);
    
    if (m_idNameSimilarMap.find(lower) != m_idNameSimilarMap.end()) {
        varp->v3warn(SIMILARNAME,
            "Declaration overlaps another with different case: "
            << varp->prettyNameQ());
    }
    m_idNameSimilarMap[lower] = varp;
}
```

### Warning Registration
```cpp
// src/V3Error.cpp
warnAdd("SIMILARNAME", WARN_DEFAULT_OFF,  // OFF by default - style warning
    "Declarations overlap with different case only");
```

### Documentation
```rst
# docs/guide/warnings.rst
.. _warn-SIMILARNAME:

SIMILARNAME
-----------

Disabled by default as this is a code-style warning; it will simulate
correctly. This is a warning as some downstream VLSI tools do
not distinguish net and gate names with the same case.
```

### Test (with typedef case)
```systemverilog
// test_regress/t/t_lint_similarname_bad.v
module t;
    logic abc = 1;
    logic ABC = 2;  // SIMILARNAME warning
    
    typedef struct { logic xyz; } S;
    S s1;
    S S1;  // SIMILARNAME warning on typedef instances
endmodule
```

---

## Example 5: Performance Optimization (Ring Buffer)

### Scenario
PR #8101: Optimize NFA ring buffer clear from O(N) to O(1).

**Reference PRs:** #8101 (Optimize NFA ring buffer), #8095 (Optimize VL_WORDS_I/VL_BYTES_I), #8061 (Optimize bounded always properties using ring buffers)

### Before
```cpp
// V3AssertNfa.cpp - old clear path
void NfaRing::clear() {
    for (auto& bit : m_ring) bit = 0;  // O(N) - clears entire vector
    m_index = 0;
    m_wrapped = false;
}
```

### After
```cpp
// V3AssertNfa.cpp - lazy invalidation
void NfaRing::reset() {
    m_liveCount = 0;      // O(1)
    m_index = 0;          // O(1)
    m_wrapped = false;    // O(1) - marks existing contents as stale
}

// On next access:
bool NfaRing::get(int idx) {
    if (!m_wrapped && idx < m_liveCount) return m_ring[idx];
    return 0;  // Stale = implicitly zero
}

void NfaRing::set(int idx, bool val) {
    if (idx >= m_liveCount) m_liveCount = idx + 1;
    m_ring[idx] = val;
}
```

### Test Verification
```python
# t_assert_perf_stats.py - asserts exact optimization count
test.file_grep(test.stats, r'NFA ring resets\s+(\d+)', EXPECTED_COUNT)
```

---

## Example 6: Parameter Array Sized by Another Parameter

### Scenario
PR #8059: Fix parameter array sized by another parameter.

**Reference PR:** #8060 (Fix untyped dtype error), #8092 (Fix NFA range ring), #8085 (Fix forceable unpacked array)

### Key Fix Pattern
```cpp
// V3Param.cpp - in ParamVisitor::visit(AstVar*)
// Handle parameter dependencies correctly during elaboration

// Before: used didWidth flag which was unreliable after V3Width
// After: use skipRefp() on dtype for typedef-safe comparison

AstNodeDType* const edtp = varp->dtypep()->skipRefp();
if (edtp->isArray()) {
    // Array size expression may reference other parameters
    // Defer sizing until all parameters resolved
    m_deferredArrayVars.insert(varp);
}
```

### Test
```systemverilog
// test_regress/t/t_param_array_size.v
module child #(parameter int SIZE = 8) (
    input logic [SIZE-1:0] data
);

module parent #(parameter int WIDTH = 16) (
    input logic [WIDTH-1:0] in_data
);
    logic [WIDTH-1:0] arr [0:3];
    child #(.SIZE(WIDTH)) c(.data(arr[0]));
endmodule
```

---

## Example 7: Four-State Logic Support

### Scenario
PR #7193: Four-state logic infrastructure (experimental).

### Key Patterns
```cpp
// New data types in include/verilated_types.h
class C4Data { uint32_t a, b; };   // 4-state char (value, xz)
class S4Data { uint32_t a, b; };   // 4-state short
class I4Data { uint64_t a, b; };   // 4-state int
class Q4Data { VlWide a, b; };     // 4-state wide

// Macros in verilatedos.h
#define VL_BITWORD_E4(bit) ((bit) / 32)  // Word index for 4-state

// Emit logic in V3EmitC*.cpp
// Use bitwise operations for 4-state AND/OR/XOR per IEEE truth tables
```

### Option Registration
```cpp
// V3Options.cpp
DECL_OPTION("--fourstate", OnOff, &m_xFourState).undocumented();
// Test: t_opt_fourstate_bad.v expects error without --fourstate
```

---

## Quick Reference: File Creation Checklist

| Task | Files to Create/Modify |
|------|------------------------|
| New pass | `V3Xxx.cpp`, `V3Xxx.h`, register in `Verilator.cpp`, test |
| New AST node | `V3AstNode*.h` (@astgen), `V3Ast.cpp` (dump/clone/isSame), parser, passes, test |
| New warning | `V3Error.cpp` (warnAdd), `docs/guide/warnings.rst`, test `_bad` or `_off` |
| Bug fix | Minimal change in relevant pass, test that FAILS without fix |
| Optimization | Change + V3Stats counter + test asserting exact count |
| New option | `V3Options.cpp` (DECL_OPTION), `.notForRerun()` if semantic-neutral, test |

---

## Debugging Tips

```bash
# Dump AST after specific pass
verilator --dumpi-tree 9 --dumpi-V3Width 9 test.v

# Dump JSON AST
verilator --dumpi-tree-json 9 --no-json-ids test.v

# Debug emit Verilog
verilator --debug-emitv --dumpi-V3EmitV 9 test.v

# Enable verbose stats
verilator --stats-vars test.v

# Coverage of test
HARNESS_UPDATE_GOLDEN=1 python3 t/test.py
```