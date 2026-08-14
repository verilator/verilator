# Verilator Project - AI Agent Instructions

## MANDATORY: Invoke Skill Router First

**Every Verilator task starts with:**

```
Skill: verilator-skill-router
```

This skill (in `agents/skills/verilator/verilator-skill-router.md`) automatically routes to the exact skills needed for your task.

## Available Skills (Auto-Loaded by Router)

| Skill | When It Triggers |
|-------|------------------|
| `verilator-onboarding` | New agent / cold start |
| `verilator-architecture` | Understanding pipeline, AST, passes |
| `verilator-coding-conventions` | Writing/modifying compiler code |
| `verilator-testing` | Adding/running tests |
| `verilator-pr-review` | **Before every PR submit** |
| `verilator-performance` | Optimization, memory, O(n^2) fixes |
| `verilator-runtime` | Runtime library (include/) fixes |
| `verilator-examples` | Copy-paste patterns for common tasks |
| `verilator-performance-guard` | **Before every commit** (10 gates) |

## Workflow for AI Agents

```
1. Task received
   |
2. Skill: verilator-skill-router  (ALWAYS FIRST)
   |
3. Read each routed skill IN ORDER
   |
4. Implement following verilator-coding-conventions
   |
5. Copy patterns from verilator-examples
   |
6. Before commit: verilator-performance-guard (10 gates)
   |
7. Before PR: verilator-pr-review (full checklist)
   |
8. make format && make cppcheck && make lint-py
   |
9. Run tests (min: make test on one OS)
```

## Token Efficiency

- **Read only routed skills** - router tells you exactly which ones
- **Copy from examples** - worked patterns, not theory
- **Checklists over re-reading** - pr-review + performance-guard are checklists

## Auto-Router Triggers (Keyword-Based)

When your task contains these keywords, the corresponding skills are automatically relevant:

| Keywords | Auto-Load Skills |
|----------|------------------|
| warning, lint, diagnostic, v3warn, v3error, Unsupported | coding-conventions, testing |
| performance, slow, O(n^2), memory leak, optimize, V3Stats, deferred | performance, performance-guard |
| runtime, verilated, VPI, trace, coverage, simulation | runtime, testing |
| parser, syntax, grammar, verilog.y, verilog.l, lexer | architecture, coding-conventions |
| assert, property, sequence, cover, V3Assert, SVA, NFA | architecture, coding-conventions, testing |
| schedule, NBA, fork, delay, V3Sched, V3Timing, V3Fork | architecture, performance, testing |
| debug, dump, dumpi, AST dump, graphviz, reproduce | debugging, testing |
| release, version, tag, Changes, ccwarn, longtests | release |
| VPI, vpi, callback, verilated_vpi | vpi, runtime |

**Rule:** If ANY keyword matches, invoke `verilator-skill-router` first -- it will confirm the routing.

## Key Files for Context

- `AGENTS.md` (this repo root) - orientation + PR checklist
- `docs/internals.rst` - authoritative architecture reference
- `agents/skills/verilator/verilator-master.md` - unified skill index

## Maintainer Feedback Patterns (Avoid These)

Top 5 rejection reasons from 40+ PRs:
1. Missing test for new diagnostic -> Add test + golden in same commit
2. O(n^2) algorithm -> Build map for batch lookup
3. Changed existing error string -> Keep wording; regen goldens if must change
4. Not const-correct -> Mark everything `const` possible
5. VN_IS + VN_AS instead of VN_CAST -> Use single conditional cast

---

**These skills work for ANY AI agent** - Claude, Codex, Cursor, or others. They encode real maintainer feedback from Verilator maintainers.