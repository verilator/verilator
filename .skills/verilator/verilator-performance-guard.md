---
name: verilator-performance-guard
description: Mandatory performance checks for every change - prevents O(n^2), memory leaks, regressions
---

# Verilator Performance Guard Skill

## Rule: Every Change Must Pass Performance Review

Before any commit, the agent MUST verify these 10 checks. This skill is **mandatory** - not optional.

---

## The 10 Performance Gates

### Gate 1: No O(n^2) Without Justification Comment
```cpp
// SCAN FOR:
for (...) { for (...) { ... } }           // Nested loops over same container
nodep->backp() in loop                      // Parent hunting = O(n^2)
foreach + linear search                     // Build map instead

// REQUIRED if O(n^2) unavoidable:
// "O(n^2) justified because: <specific reason, e.g., N < 10 always>"
```

### Gate 2: Const-Correctness (Enables Compiler Optimization)
```cpp
// EVERY variable, parameter, pointer, member function:
// - Mark const where possible
// - Pointers: Type* const ptr (doubly const)
// - Methods: void foo() const

// VERIFY: grep -r "const" changed files - should be pervasive
```

### Gate 3: VN_CAST Single Conditional Cast
```cpp
// BANNED: VN_IS + VN_AS pair
if (VN_IS(nodep, Type)) { VN_AS(nodep, Type); }

// REQUIRED: VN_CAST
if (const Type* const ptr = VN_CAST(nodep, Type)) { ... }
```

### Gate 4: skipRefp() on ALL dtype Comparisons
```cpp
// BANNED: dtypep()->width(), dtypep()->isFoo()
// REQUIRED: dtypep()->skipRefp()->width(), dtypep()->skipRefp()->isFoo()

// Missing skipRefp() = typedef bugs (silent correctness issues)
```

### Gate 5: No Static/Global Mutable Data
```cpp
// BANNED: static int counter;  // Breaks parallelism
// BANNED: global map/cache     // Breaks parallelism

// REQUIRED: Pass state through visitor members + VL_RESTORER
// Or use per-module maps (std::map) that get destroyed
```

### Gate 6: Deferred Deletion in Visitors
```cpp
// BANNED: deleteTree(nodep) in visitor
// REQUIRED: VL_DO_DANGLING(pushDeletep(nodep), nodep)

// deleteTree() ONLY for fresh nodes that never entered tree
```

### Gate 7: VMemberMap/findMember for Name Lookups
```cpp
// BANNED: Linear search through vectors/lists for names
// REQUIRED: VMemberMap (O(1)) or std::map (O(log n))

// VMemberMap handles scope hierarchy automatically
```

### Gate 8: AstForeach Not Unrolled Loops
```cpp
// BANNED: Manual unrolling generating O(N) code
for (int i=0; i<N; ++i) { ... }

// REQUIRED: AstForeach - constant code size
new AstForeach{fl, varp, rangeLowp, rangeHighp, bodyp}
```

### Gate 9: reserve()/emplace for Containers
```cpp
// BANNED: push_back in loop without reserve
// REQUIRED: vector.reserve(est); map.emplace(key, val)

// Check .second of emplace instead of separate find()
```

### Gate 10: V3Stats Counter for New Pass Work
```cpp
// REQUIRED: Every new pass adds stats
V3Stats::addStat("pass_name", "metric", count);

// Stats become deterministic regression anchors
// CI catches performance regressions automatically
```

---

## Automated Verification Script

Add to CI or run locally:

```bash
#!/bin/bash
# performance-gate.sh - run before commit

echo "=== Gate 1: O(n^2) patterns ==="
grep -rn "backp()" src/*.cpp | grep -v "VL_RESTORER" && echo "FAIL: backp() in loop" || echo "OK"

echo "=== Gate 2: Const-correctness ==="
# Heuristic: check for non-const pointers in new code
git diff --name-only | xargs grep -L "const" | grep "\.cpp$" && echo "WARN: Files without const" || echo "OK"

echo "=== Gate 3: VN_CAST vs VN_IS+VN_AS ==="
git diff src/ | grep -E "VN_IS.*VN_AS|VN_AS.*VN_IS" && echo "FAIL: VN_IS+VN_AS pair" || echo "OK"

echo "=== Gate 4: skipRefp() ==="
git diff src/ | grep -E "dtypep\(\)->(width|is)" | grep -v "skipRefp" && echo "FAIL: missing skipRefp" || echo "OK"

echo "=== Gate 5: Static mutable ==="
git diff src/ | grep "^+.*static.*[^const]" && echo "FAIL: new static mutable" || echo "OK"

echo "=== Gate 6: deleteTree in visitor ==="
git diff src/ | grep "deleteTree" && echo "FAIL: deleteTree in visitor" || echo "OK"

echo "=== Gate 7: VMemberMap ==="
git diff src/ | grep -E "find.*name|name.*find" | grep -v "VMemberMap\|findMember" && echo "WARN: linear name search" || echo "OK"

echo "=== Gate 8: AstForeach ==="
git diff src/ | grep -E "for.*int.*=.*0.*<.*size" && echo "WARN: possible unrolled loop" || echo "OK"

echo "=== Gate 9: reserve/emplace ==="
git diff src/ | grep "push_back" && echo "WARN: push_back without reserve" || echo "OK"

echo "=== Gate 10: V3Stats ==="
git diff src/ | grep -E "V3Stats::addStat" || echo "WARN: no V3Stats in new pass"
```

---

## Performance Anti-Patterns Cheat Sheet

| Anti-Pattern | Detection | Fix |
|--------------|-----------|-----|
| `backp()` in loop | `grep "backp()" file.cpp` | Build parent map in forward walk |
| Linear name search | `grep "name() ==" file.cpp` | `VMemberMap::findMember()` |
| `VN_IS` + `VN_AS` | `grep -A2 "VN_IS" file.cpp` | `VN_CAST` single cast |
| Missing `skipRefp()` | `grep "dtypep()->" file.cpp \| grep -v skipRefp` | Add `->skipRefp()` |
| `deleteTree()` in visitor | `grep "deleteTree" file.cpp` | `VL_DO_DANGLING(pushDeletep)` |
| Static mutable | `grep "static.*[^const]" file.cpp` | Remove or make thread-local |
| Unrolled loop | `grep "for.*size()" file.cpp` | `AstForeach` |
| `push_back` no reserve | `grep "push_back" file.cpp` | `reserve()` + `emplace` |
| No V3Stats | New pass file without stats | Add `V3Stats::addStat()` calls |

---

## Memory Leak Prevention Checklist

- [ ] Every `new AstNode` has matching `VL_DO_DANGLING(pushDeletep)` or ownership transfer
- [ ] Map/set keys using raw node pointers -> erase on node deletion
- [ ] No static/global containers holding node pointers
- [ ] `cloneRelink()` propagates all stateful flags (`maybePointedTo`, etc.)
- [ ] `broken()` override for cross-tree pointers
- [ ] `VNUser1InUse/VNUser2InUse` guards document user field ownership

---

## Integration: How to Use This

1. **Before writing code**: Read `verilator-performance-guard`
2. **During implementation**: Apply gates 1-10 as you write
3. **Before commit**: Run the verification script (or mental checklist)
4. **On review**: Explicitly state "Performance gates 1-10 verified"

### Efficient Usage:
- Read once, internalize; don't re-read every turn
- Use the **cheat sheet table** for quick reference
- The verification script can be run as a pre-commit hook

### Mandatory Invocation:
```
User: "Fix this bug / Add this feature"
Agent: [Reads verilator-performance-guard] -> Implements with gates -> Verifies
```

---

## CI Integration (Future)

Add to `.github/workflows/ci.yml`:
```yaml
- name: Performance Gates
  run: |
    bash .skills/verilator/performance-gate.sh
```

This makes performance **non-optional** - every PR automatically checked.