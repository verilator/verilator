# FSM Coverage Test Guide

<!--
SPDX-FileCopyrightText: 2026 Wilson Snyder
SPDX-License-Identifier: CC0-1.0
-->

This note explains the FSM-focused regression tests under `test_regress/t/` and how they are grouped.

## Core Detection

- `t_cover_fsm_basic`: canonical one-block FSM with reset arcs and annotated coverage output.
  - proves the baseline single-register one-block `if (rst) case (state)` extraction path
- `t_cover_fsm_two_proc_multi`: grouped supported two-process and three-block styles, plus nearby supported core variants and nearby unsupported shapes that should stay uninferred.
  - direct two-process extraction
  - three-block extraction
  - direct ternary extraction
  - `always @*` supported extraction
  - explicit combinational sensitivity-list extraction
- `t_cover_fsm_beginif`: supported `begin/end` wrapping inside transition branches.
  - proves that branch-local block structure does not prevent one-block arc extraction

## Reset Semantics

- `t_cover_fsm_reset`: grouped simulator-style reset semantics.
  - baseline reset include/exclude behavior
  - extra constant reset writes that still preserve reset extraction
  - one-block reset mismatch fallback that preserves the FSM
  - one-block non-constant reset fallback that preserves the FSM
- `t_cover_fsm_reset_multi`: grouped warning-oriented reset-policy cases.
  - multiple reset writes to the same state variable warn and suppress reset-arc modeling
  - nearby reset-policy warnings stay attached to supported FSM detection rather than silent mis-modeling
- `t_cover_fsm_reset_then_bad`: reset branch with non-constant assignment is ignored for reset arcs.
  - the FSM stays legal, but reset-arc extraction must not invent a constant reset state
- `t_cover_fsm_reset_commit_mismatch_bad`: reset branch writes a different register than the commit path.
  - two-process reset extraction must reject when reset and commit do not target the same state register
- `t_cover_fsm_reset_unknown_enum_bad`: reset arc is filtered when it assigns a constant outside the declared enum.
  - enum labels define the legal reset destinations for modeled reset arcs

## Plain `always` Warning Scan

- `t_cover_fsm_plain_always_warn_multi_bad`: grouped warning-only near-FSM plain edge-sensitive `always` cases.
  - selector is `state_q`
  - selector is `state_d`
  - `default` is only supported because `fsm_arc_include_cond` is enabled
- `t_cover_fsm_plain_always_ignore_multi_bad`: grouped plain-`always` shapes the warning scan must ignore silently.
  - non-`VarRef` selector
  - unrelated selector
- `t_cover_fsm_plain_always_case_next_noncano_bad`: `case(state_d)` plain-`always` shape without the canonical pre-case default.
  - warning scan sees the nearby structure but must reject the non-canonical next-state default pattern
- `t_cover_fsm_plain_always_noassign_bad`: selector matches, but case items never assign the next-state variable.
  - warning scan must ignore a near miss that never actually drives the candidate next-state register
- `t_cover_fsm_nextstate_overwrite_warn`: next-state default is overwritten before the case and should warn.
  - canonical `state_d = state_q` default is present, but a later overwrite before `case (state_d)` makes the pattern unsupported

This family is intentionally still split across multiple tests because it has
three different observable outcomes:

- compile-time warning goldens
- header-only silent-ignore `coverage.dat` goldens
- silent-ignore `coverage.dat` files that still contain zero-hit FSM records

So this category is organized by behavior first, not forced into a single file.

## Normalized-If and `case(state_d)` Reject Shapes

- `t_cover_fsm_normalized_if_multi_bad`: grouped negative shapes that should not be extracted as FSM arcs.
  - one-armed `if`
  - non-constant then branch
  - non-constant else branch
  - mismatched branch temporaries
  - mixed state/temp branch writes
  - same-temp branches with no final commit
  - follow-up assignment that is not `state_d = temp`
  - follow-up assignment from the wrong temp
  - follow-up assignment to the wrong lhs
  - `case(state_d)` with a wrong pre-case RHS
- `t_cover_fsm_case_next_ok_multi`: grouped accepted canonical `case(state_d)` forms.
  - accepted canonical `case(state_d)` with an unrelated pre-case bit-select assignment
  - accepted canonical `case(state_d)` with an unrelated pre-case plain `VarRef` assignment

This category is intentionally split into:

- one grouped reject file
- one grouped accepted canonical `case(state_d)` file

That keeps the output styles coherent while still matching the behavioral theme.

## Transition-Shape Rejects

- `t_cover_fsm_transition_shapes_multi_bad`: grouped unsupported transition-shape patterns that must not emit FSM points.
  - direct case-item assignment with plain `VarRef` RHS
  - direct ternary case item with non-constant then arm
  - direct ternary case item with non-constant else arm
  - one-block conditional commit with non-constant reset arm
  - one-block conditional commit whose non-reset arm is not a plain source `VarRef`
  - combinational case selector that is not a plain state `VarRef`

## Validation and Policy

- `t_cover_fsm_if_unknown_enum_multi_bad`: grouped conditional-transition warnings for unknown enum constants on either ternary arm.
- `t_cover_fsm_policy_accept_multi`: grouped accepted policy-style forms.
  - accepted `fsm_arc_include_cond` style coverage
  - accepted default-item arc when `fsm_arc_include_cond` is enabled
  - accepted forced-FSM extraction for non-enum state variables
- `t_cover_fsm_forced_wide_bad`: forced FSM is rejected when the state width is too wide.
  - `/*verilator forceable*/` or forced-FSM style hints do not override the supported width limit
- `t_cover_fsm_enum_bad`: invalid enum setup that must not be accepted.
  - malformed or unsupported enum-backed state declarations must not be inferred as legal FSMs
- `t_cover_fsm_enumwide_bad`: enum-backed state too wide for supported FSM coverage.
  - enum typing alone is not enough if the state width exceeds the supported range

This family is intentionally still split because it currently mixes:

- accepted simulator-style policy checks
- warning-oriented policy checks
- silent-ignore width-limit checks

So only the accepted simulator-style subset is grouped today.

## Multi-Candidate and Warning Policy

- `t_cover_fsm_combo_same_warn_bad`: same-module combo candidates that should warn.
  - multiple combinational candidates for the same state register must produce a warning, not duplicate FSMs
- `t_fsmmulti_combo_multi_warn_bad`: grouped multi-candidate combo-warning cases.
  - related combinational multi-candidate warning shapes share one warning-oriented surface
- `t_fsmmulti_same_bad`: duplicate same-state candidates.
  - repeated candidates for the same logical FSM should not produce duplicate modeled machines
- `t_fsmmulti_warn_bad`: baseline multi-candidate warning behavior.
  - generic FSMMULTI warning policy for ambiguous detection sites
- `t_fsmmulti_warn_off`: multi-candidate warnings disabled.
  - warning suppression controls should disable FSMMULTI noise without changing extraction semantics

## Feature-Level Negative Tests

- `t_cover_fsm_flag_off`: `--coverage-fsm` disabled, so no FSM points should appear.
- `t_cover_fsm_negative_extract`: nearby negative extraction shapes that should stay uninferred.
- `t_cover_fsm_noreset`: FSM extraction without reset arcs.
- `t_cover_fsm_graphdump`: graph-dump side outputs for FSM extraction.
  - verifies the graph dump still names and emits the expected FSM structures
- `t_cover_fsm_decldump`: declaration-dump side outputs for FSM extraction.
  - verifies the declaration dump still names and emits the expected FSM coverage declarations

## Tooling and Reporting

- `t_vlcov_fsm_report`: report-generation coverage checks for FSM coverage output formatting and content.
  - verifies `verilator_coverage` report presentation for FSM state and arc data

## Notes

- Tests ending in `_ok` keep the FSM and usually check annotated or summary output.
- Tests ending in `_bad` usually prove a specific unsupported shape stays silent, warns, or avoids FSM arc extraction.
- The grouped `*_multi*` tests are the preferred shape for new additions when multiple nearby scenarios can share one user-facing regression surface.
