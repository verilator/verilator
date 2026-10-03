<!-- DESCRIPTION: Verilator: Experimental subgraph scheduling proposal
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# Experimental subgraph scheduling

This proof of concept explores reducing Verilation work for repeated module
instances. It preserves a selected module as a scheduling boundary, orders its
logic locally, and reuses eligible evaluation bodies across instances of the
same elaborated module. Each instance retains its own simulation state.

The intended benefit is less repeated procedure expansion and scheduling, with
less generated C++ for the child bodies. Per-instance state, port connections,
input acquisition, and calls remain necessary. This is an experimental,
opt-in facility, not a general replacement for the flat scheduler.

## Upstream baseline

This series is based on `ceb7dde93881ea50ab6463a8834ae8572476a97d`,
the parent of `f458e4006` (Move module inlining after V3Scope).
It keeps the upstream ordering of Inline before Inst and Scope. Adapting
sharing to newer upstream revisions is a separate integration task.

## Selecting a boundary

The implementation series introduces `--subgraph-schedule`, disabled by
default, and either of these module selectors:

```systemverilog
module child (...);
  /*verilator subgraph_boundary*/
  ...
endmodule
```

```text
`verilator_config
subgraph -module "child"
```

Selection preserves the module through inlining. Local scheduling and early
procedure sharing have separate eligibility checks. A selected instance that
cannot be scheduled locally remains in the ordinary parent scheduler;
`SUBGRAPHFALLBACK` identifies the first failed condition and its RTL location.

## Scheduling and state ownership

The implementation uses the existing AST, NBA lowering, region partitioning,
and Order machinery. It does not introduce a second RTL representation or a
separate simulation model.

At a clock event, input acquisition and next-state evaluation must precede
publication of new child outputs. Evaluation and commit/publication therefore
remain separate operations in the parent dependency graph. In particular,
two children connected by a registered feedback path must both observe the
old state on that edge, regardless of their call order.

Local combinational logic is also evaluated when inputs change. Output
combinational logic and publication run during initial settling and after
state commits, as required by the existing evaluation regions.

For sharing, one representative scope owns the procedure bodies. Receiver
scopes retain their own state and invoke the shared functions with their own
receiver pointers. Boundary contracts describe the effects visible to the
parent without exposing every internal state dependency. Optimizations must
preserve this receiver-relative interpretation until Descope converts it to
generated C++ calls.

## Scope of the proof of concept

Local scheduling starts with a single rising-edge clock and compatible child
logic. Multiple clocks, generated-clock dependencies, zero-delay scheduling,
unsupported timing controls, and combinational cycles can require fallback.
Eligibility is checked on the transformed AST, so the exact accepted shapes
are defined by the implementation and accompanying tests. Output analysis
rejects identified input feedthrough paths, but admits unknown local sources;
it is not a complete proof of output provenance.

Early sharing has stricter requirements than local scheduling. It requires
compatible instances of the same elaborated specialization, supported local
procedures and input connections, and single-threaded compilation. Failure
to share does not itself imply failure to schedule locally. Inline expands
intermediate modules before early sharing is checked. The early check
requires the elaborated cell count to equal the total instance count.

The series retains the source branch's extensions for combinational writes,
input aliases, and output provenance. Admission follows combinational
feedthrough rather than the original instance hierarchy. DFG can place
parent expressions inside a child and create cross-boundary reads of internal
temporaries. These values also participate in output-cone analysis and parent
contracts. Local settling and post-commit output evaluation order publication
assignments together with the output cone, including expressions that read
published ports.
Tests cover both enabled and disabled operation, phase ordering,
fallback diagnostics, state independence, and generated-function sharing.

## Implementation responsibilities

`V3SubgraphBoundary` retains port identities, connection metadata, and RTL
locations across elaboration, pin lowering, scoping, and NBA lowering.
`V3SubgraphSharing` checks early sharing and creates per-instance input
captures before Scope expands procedures. Inst retains its normal pin
lowering; Scope retains representative bodies and independent receiver state.

`V3SchedSubgraphEligibility` checks transformed logic and records fallback
causes. `SubgraphPlan` in `V3SchedSubgraph` owns admitted logic and local
partitioning, replication, settling, and input-combinational evaluation.
`V3SchedSubgraphNba` orders next-state and publication functions, reuses
compatible bodies, and emits receiver calls. These helpers use the existing
scheduler and Order graph through explicit port contracts and phase edges.
There is no separate subgraph RTL representation.

The commit series starts from the upstream baseline above. It introduces the
proposal, selectors, boundary metadata, local scheduling with fallback, and
early sharing, with regression tests next to the behavior they exercise.
