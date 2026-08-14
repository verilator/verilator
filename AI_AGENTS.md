# Verilator -- Multi-Agent AI Configuration

This file documents how Verilator skills work across different AI coding agents.

## Skill Location

All Verilator skills live in one canonical location:

```
agents/skills/verilator/
```

## Agent Integration

### Claude Code (Native)
- Reads `agents/skills/verilator/` directly
- Reads `CLAUDE.md` at repo root
- Reads `AGENTS.md` at repo root and per-directory

### Codex (Via Symlink)
```bash
# To enable Codex to read the same skills, symlink the directory:
ln -s ../agents/skills/verilator .codex/skills/verilator
```
- Reads skills from `.codex/skills/verilator/` (after the symlink above is created)
- Reads `AGENT.md` at repo root (Codex equivalent of CLAUDE.md)

### Generic Agents (Any Tool)
All agents can use the skills by:
1. Reading `agents/skills/verilator/verilator-skill-router.md` first
2. Following the routing to other skills
3. The skills are plain Markdown - no tool-specific formatting

---

## Unified Entry Points

| Agent | Primary Config | Skills Directory |
|-------|----------------|------------------|
| Claude Code | `CLAUDE.md` | `agents/skills/verilator/` |
| Codex | `AGENT.md` | `.codex/skills/verilator/` (symlink required) |
| Generic | `AI_AGENTS.md` | Any path to `agents/skills/verilator/` |

---

## Quick Setup for New Agents

```bash
# For any agent, run from verilator repo root:

# 1. Ensure skills are accessible (symlink if needed)
ln -sf agents/skills/verilator /path/to/agent/skills/verilator

# 2. Read the router first
cat agents/skills/verilator/verilator-skill-router.md

# 3. Follow its routing for your task
```

---

## Skill Invocation Syntax by Agent

| Agent | Syntax |
|-------|--------|
| Claude Code | `Skill: verilator-skill-router` or `/skill verilator-skill-router` |
| Codex | `@verilator-skill-router` or "Use verilator-skill-router skill" |
| Generic | "Read and follow verilator-skill-router.md" |

---

## Mandatory Workflow (All Agents)

```
1. ALWAYS start with: verilator-skill-router
2. Read each routed skill IN ORDER
3. Implement following verilator-coding-conventions
4. Copy patterns from verilator-examples
5. Before commit: verilator-performance-guard (10 gates)
6. Before PR: verilator-pr-review (full checklist)
7. make format && make cppcheck && make lint-py
8. Run tests (min: make test on one OS)
```

---

## Token Efficiency

- Skills are **modular** -- router tells you exactly which to read
- **Copy from examples** -- worked patterns, not theory
- **Checklists over re-reading** -- pr-review + performance-guard are 30-second checklists

---

## Maintainer Feedback Patterns (All Agents)

Top 5 rejection reasons from 40+ PRs:
1. Missing test for new diagnostic -> Add test + golden in same commit
2. O(n^2) algorithm -> Build map for batch lookup
3. Changed existing error string -> Keep wording; regen goldens if must change
4. Not const-correct -> Mark everything `const` possible
5. VN_IS + VN_AS instead of VN_CAST -> Use single conditional cast

---

## Files Created

| File | Purpose |
|------|---------|
| `agents/skills/verilator/verilator-skill-router.md` | **ALWAYS FIRST** - routes task to skills |
| `agents/skills/verilator/verilator-onboarding.md` | 5-min mental model for new agents |
| `agents/skills/verilator/verilator-architecture.md` | Pipeline, AST, visitors, passes |
| `agents/skills/verilator/verilator-coding-conventions.md` | C++ style, AST rules, visitors, errors |
| `agents/skills/verilator/verilator-testing.md` | Test structure, drivers, goldens |
| `agents/skills/verilator/verilator-pr-review.md` | Maintainer feedback, pre-PR checklist |
| `agents/skills/verilator/verilator-performance.md` | Memory, O(n^2) elimination, perf patterns |
| `agents/skills/verilator/verilator-runtime.md` | include/ library: C++14, fixed-width, threads |
| `agents/skills/verilator/verilator-examples.md` | Worked examples: pass, AST node, bug, warning |
| `agents/skills/verilator/verilator-performance-guard.md` | 10 mandatory performance gates |
| `agents/skills/verilator/verilator-master.md` | Unified skill index + decision map |
| `agents/skills/verilator/verilator-debugging.md` | Debug AST dumps, --dumpi-*, JSON, graphviz |
| `agents/skills/verilator/verilator-parser.md` | Lexer/grammar: tokens, precedence, //UNSUP |
| `agents/skills/verilator/verilator-release.md` | Release process: ccwarn, longtests, version, tagging |
| `agents/skills/verilator/verilator-vpi.md` | VPI callbacks, verilated_vpi.cpp, --vpi vs --vpi-lazy |
| `CLAUDE.md` | Claude Code entry point |
| `AGENTS.md` | Updated with skills reference |
| `AI_AGENTS.md` | This file - multi-agent guide |
