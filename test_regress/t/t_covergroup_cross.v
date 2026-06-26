// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test cross coverage: 2-way, 3-way, and 4-way crosses

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [1:0] addr;
  logic cmd;
  logic mode;
  logic parity;
  logic [63:0] wide;
  logic [3:0] state;
  logic [3:0] val;

  typedef struct packed {logic m_p; logic h_mode;} cfg_t;
  cfg_t s_cfg = '0;

  // 2-way cross
  covergroup cg2;
    cp_addr: coverpoint addr {bins addr0 = {0}; bins addr1 = {1};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    addr_cmd: cross cp_addr, cp_cmd;
  endgroup

  // 3-way cross
  covergroup cg3;
    cp_addr: coverpoint addr {bins addr0 = {0}; bins addr1 = {1}; bins addr2 = {2};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    cp_mode: coverpoint mode {bins normal = {0}; bins debug = {1};}
    addr_cmd_mode: cross cp_addr, cp_cmd, cp_mode;
  endgroup

  // 4-way cross
  covergroup cg4;
    cp_addr: coverpoint addr {bins addr0 = {0}; bins addr1 = {1};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    cp_mode: coverpoint mode {bins normal = {0}; bins debug = {1};}
    cp_parity: coverpoint parity {bins even = {0}; bins odd = {1};}
    addr_cmd_mode_parity: cross cp_addr, cp_cmd, cp_mode, cp_parity;
  endgroup

  // Cross with option set inside the cross body
  covergroup cg5;
    cp_addr: coverpoint addr {bins addr0 = {0}; bins addr1 = {1};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    addr_cmd_opt: cross cp_addr, cp_cmd{option.weight = 2;}
  endgroup

  // 2-way cross where one coverpoint uses a range bin
  covergroup cg_range;
    cp_addr: coverpoint addr {
      bins lo_range = {[0 : 1]};  // range bin
      bins hi_range = {[2 : 3]};
    }
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    addr_cmd_range: cross cp_addr, cp_cmd;
  endgroup

  // Cross where one coverpoint has ignore_bins - ignored values must not appear in cross bins
  covergroup cg_ignore;
    cp_addr: coverpoint addr {
      ignore_bins ign = {3};  // addr=3 excluded from cross
      bins a0 = {0};
      bins a1 = {1};
    }
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    cross_ab: cross cp_addr, cp_cmd;
  endgroup

  // Cross with option.at_least set in the cross body
  covergroup cg_at_least;
    cp_addr: coverpoint addr {bins addr0 = {0}; bins addr1 = {1};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    addr_cmd_al: cross cp_addr, cp_cmd{option.at_least = 3;}
  endgroup

  // Cross with option.goal set in the cross body
  covergroup cg_goal;
    cp_addr: coverpoint addr {bins addr0 = {0}; bins addr1 = {1};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    addr_cmd_goal: cross cp_addr, cp_cmd{option.goal = 90;}
  endgroup

  // Cross with an unsupported option (option.per_instance) - Verilator warns and ignores it
  covergroup cg_unsup_cross_opt;
    cp_addr: coverpoint addr {bins addr0 = {0}; bins addr1 = {1};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    addr_cmd_unsup: cross cp_addr, cp_cmd{
      option.per_instance = 1;  // unsupported for cross - expect COVERIGN warning
    }
    // Non-standard hierarchical reference as a cross item (an implicit coverpoint):
    // accepted with NONSTD, but implicit coverpoints are unsupported so the whole
    // cross is dropped (COVERIGN, suppressed here) - it contributes no bins.
    /* verilator lint_off NONSTD */
    cross_hier: cross cp_addr, s_cfg.m_p;
    /* verilator lint_on NONSTD */
  endgroup

  // Covergroup with an unnamed cross - the cross is reported under the default name "cross"
  covergroup cg_unnamed_cross;
    cp_a: coverpoint addr {bins a0 = {0}; bins a1 = {1};}
    cp_c: coverpoint cmd {bins read = {0}; bins write = {1};}
    cross cp_a, cp_c;  // no label: reported under the default cross name
  endgroup

  // Cross plus an un-crossed coverpoint: get_inst_coverage must combine the un-crossed
  // coverpoint cp_solo with the cross and its crossed coverpoints.
  covergroup cg_mixed;
    cp_addr: coverpoint addr {bins addr0 = {0}; bins addr1 = {1};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    cp_solo: coverpoint mode {bins normal = {0}; bins debug = {1};}  // not crossed
    ab: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint that also has a default bin: exercises default-bin handling on a
  // coverpoint that feeds a cross.
  covergroup cg_def_cross;
    cp_a: coverpoint addr iff (mode) {bins a0 = {0}; bins a1 = {1}; bins ad = default;}
    cp_c: coverpoint cmd {bins read = {0}; bins write = {1};}
    axc: cross cp_a, cp_c;
  endgroup

  // Crossed coverpoint with an array range bin (bins av[] = {[0:1]}): exercises the
  // coverpoint hit-list sizing for array range elements feeding a cross.
  covergroup cg_arr_range;
    cp_addr: coverpoint addr {bins av[] = {[0 : 1]};}  // -> av[0]=0, av[1]=1
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    ar: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint with an array value bin (bins av[] = {0, 2}): array value elements.
  covergroup cg_arr_vals;
    cp_addr: coverpoint addr {bins av[] = {0, 2};}  // -> av[0]=0, av[1]=2
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    av: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint with a wildcard array bin (wildcard bins wb[] = {2'b0?}): the '0?'
  // wildcard expands to addr values 0 and 1, each its own array element.
  covergroup cg_wild_arr;
    cp_addr: coverpoint addr {wildcard bins wb[] = {2'b0?};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    wa: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint with a non-array wildcard bin (wildcard bins wb = {2'b0?}): single
  // wildcard bin matching addr 0 or 1, feeding a cross.
  covergroup cg_wild_solo;
    cp_addr: coverpoint addr {wildcard bins wb = {2'b0?};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    ws: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint with a four-state literal in a non-wildcard array bin
  // (bins av[] = {2'b0x}): LRM 1800-2023 19.5.4 permits 4-state values in a bin definition.
  // The hit-list sizing cannot statically analyze a 4-state value, so it falls back to the
  // safe slot count.  Under Verilator's 2-state simulation the value matches addr=0.
  covergroup cg_arr_4state;
    cp_addr: coverpoint addr {bins av[] = {2'b0x};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    a4: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint with two *overlapping* Normal range bins (addr=1 is in both lo and
  // hi): the hit-list sizing must report a bound > 1 (a single sample can fall in two bins),
  // exercising the max-overlap computation in computeHitListBound.
  covergroup cg_overlap;
    cp_addr: coverpoint addr {bins lo = {[0 : 1]}; bins hi = {[1 : 2]};}  // overlap at addr=1
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    ov: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint whose sampled expression is wider than 64 bits: exercises the
  // width>=64 max-value path in the hit-list sizing (where 1<<width would overflow).
  covergroup cg_wide;
    cp_wide: coverpoint wide {bins lo = {[0 : 1]}; bins hi = {[2 : 3]};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    wd: cross cp_wide, cp_cmd;
  endgroup

  // Crossed coverpoint with open-ended ('$') range bins: 'lo' is open-low ([$:1]) and 'hi'
  // is open-high ([2:$]); exercises the unbounded-bound interval handling in the hit-list
  // sizing (lo clamps to 0, hi clamps to the type max).
  covergroup cg_openrange;
    cp_addr: coverpoint addr {bins lo = {[$ : 1]}; bins hi = {[2 : $]};}
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    orc: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint with an inverted range bin (lo bound > hi bound): the bin matches no
  // value, so the hit-list sizing rejects it (lo > hi) and falls back to the safe slot count.
  // The 'inv' bin and its cross bins are therefore never hit (coverage stays at 40%).
  covergroup cg_inv;
    cp_addr: coverpoint addr {bins inv = {[3 : 0]};}  // inverted -> never matches
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    iv: cross cp_addr, cp_cmd;
  endgroup

  // Crossed coverpoint with *no* Normal bins (only ignore_bins): the cross has an empty bin
  // product, so the hit-list sizing returns the safe bound of 1.  Coverage is the cmd
  // coverpoint alone (vacuously 100% once both cmd bins are hit).
  covergroup cg_noNormal;
    cp_addr: coverpoint addr {ignore_bins ig = {[0 : 3]};}  // zero Normal bins
    cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
    nn: cross cp_addr, cp_cmd;
  endgroup

  // Cross of a *transition* coverpoint with a value coverpoint.  Transition coverpoints route
  // through the VlCoverpoint runtime (their completion appends to the hit list), so a cross
  // can read them like any other coverpoint.
  covergroup cg_trans;
    cp_t: coverpoint state {bins t01 = (0 => 1);}  // one Normal (transition) bin
    cp_v: coverpoint val {bins v5 = {5}; bins v6 = {6};}
    tx: cross cp_t, cp_v;
  endgroup

  cg2 cg2_inst = new;
  cg_ignore cg_ignore_inst = new;
  cg_range cg_range_inst = new;
  cg3 cg3_inst = new;
  cg4 cg4_inst = new;
  cg5 cg5_inst = new;
  cg_at_least cg_at_least_inst = new;
  cg_goal cg_goal_inst = new;
  cg_unsup_cross_opt cg_unsup_cross_opt_inst = new;
  cg_unnamed_cross cg_unnamed_cross_inst = new;
  cg_mixed cg_mixed_inst = new;
  cg_def_cross cg_def_cross_inst = new;
  cg_arr_range cg_arr_range_inst = new;
  cg_arr_vals cg_arr_vals_inst = new;
  cg_wild_arr cg_wild_arr_inst = new;
  cg_wild_solo cg_wild_solo_inst = new;
  cg_arr_4state cg_arr_4state_inst = new;
  cg_overlap cg_overlap_inst = new;
  cg_wide cg_wide_inst = new;
  cg_openrange cg_openrange_inst = new;
  cg_inv cg_inv_inst = new;
  cg_noNormal cg_noNormal_inst = new;
  cg_trans cg_trans_inst = new;

  initial begin
    // Sample 2-way: hit all 4 combinations
    // cg2: 2 cp bins + 2 cp bins + 4 cross bins = 8 bins total (flat count)
    addr = 0;
    cmd = 0;
    mode = 0;
    parity = 0;
    cg2_inst.sample();  // addr0 x read
    `checkr(cg2_inst.get_inst_coverage(), 37.5);  // 3/8: addr0, read, addr0_x_read
    addr = 1;
    cmd = 1;
    mode = 0;
    parity = 0;
    cg2_inst.sample();  // addr1 x write
    `checkr(cg2_inst.get_inst_coverage(), 75.0);  // 6/8: all cp bins + 2 cross bins
    addr = 0;
    cmd = 1;
    mode = 0;
    parity = 0;
    cg2_inst.sample();  // addr0 x write
    `checkr(cg2_inst.get_inst_coverage(), 87.5);  // 7/8: 3 cross bins hit
    addr = 1;
    cmd = 0;
    mode = 0;
    parity = 0;
    cg2_inst.sample();  // addr1 x read
    `checkr(cg2_inst.get_inst_coverage(), 100.0);  // 8/8: all 4 cross bins hit

    // Sample 3-way: hit 4 of 12 combinations
    // cg3: 3+2+2+12=19 bins; 4 cross bins hit -> 11/19=57.9% (not clean; no intermediate checkr)
    addr = 0;
    cmd = 0;
    mode = 0;
    cg3_inst.sample();  // addr0 x read x normal
    addr = 1;
    cmd = 1;
    mode = 0;
    cg3_inst.sample();  // addr1 x write x normal
    addr = 2;
    cmd = 0;
    mode = 1;
    cg3_inst.sample();  // addr2 x read x debug
    addr = 0;
    cmd = 1;
    mode = 1;
    cg3_inst.sample();  // addr0 x write x debug

    // Sample 4-way: hit 4 of 16 combinations
    // cg4: 2+2+2+2+16=24 bins; 4 cross bins hit -> 12/24=50%
    addr = 0;
    cmd = 0;
    mode = 0;
    parity = 0;
    cg4_inst.sample();
    addr = 1;
    cmd = 1;
    mode = 0;
    parity = 1;
    cg4_inst.sample();
    `checkr(cg4_inst.get_inst_coverage(), 37.5);  // 9/24: all cp bins + 2 cross bins
    addr = 0;
    cmd = 1;
    mode = 1;
    parity = 0;
    cg4_inst.sample();
    addr = 1;
    cmd = 0;
    mode = 1;
    parity = 1;
    cg4_inst.sample();
    `checkr(cg4_inst.get_inst_coverage(), 50.0);  // 12/24: all cp bins + 4 cross bins

    // Sample cg5 (cross with option.weight=2; weight is ignored in flat bin count)
    // cg5: 2+2+4=8 bins; 2 cross bins hit -> 6/8=75%
    addr = 0;
    cmd = 0;
    cg5_inst.sample();
    `checkr(cg5_inst.get_inst_coverage(), 37.5);  // 3/8: addr0, read, addr0_x_read
    addr = 1;
    cmd = 1;
    cg5_inst.sample();
    `checkr(cg5_inst.get_inst_coverage(), 75.0);  // 6/8: all cp bins + 2 cross bins

    // Sample cg_ignore: addr=3 is in ignore_bins so no cross bins for it
    // cg_ignore: 2+2+4=8 bins total
    addr = 0;
    cmd = 0;
    cg_ignore_inst.sample();  // a0 x read
    `checkr(cg_ignore_inst.get_inst_coverage(), 37.5);  // 3/8
    addr = 1;
    cmd = 1;
    cg_ignore_inst.sample();  // a1 x write
    `checkr(cg_ignore_inst.get_inst_coverage(), 75.0);  // 6/8
    addr = 0;
    cmd = 1;
    cg_ignore_inst.sample();  // a0 x write
    `checkr(cg_ignore_inst.get_inst_coverage(), 87.5);  // 7/8
    addr = 1;
    cmd = 0;
    cg_ignore_inst.sample();  // a1 x read
    `checkr(cg_ignore_inst.get_inst_coverage(), 100.0);  // 8/8
    addr = 3;
    cmd = 0;
    cg_ignore_inst.sample();  // ignored (addr=3 in ignore_bins)
    `checkr(cg_ignore_inst.get_inst_coverage(), 100.0);  // still 100%

    // Sample range-bin cross
    // cg_range: 2+2+4=8 bins
    addr = 0;
    cmd = 0;
    cg_range_inst.sample();  // lo_range x read
    `checkr(cg_range_inst.get_inst_coverage(), 37.5);  // 3/8
    addr = 2;
    cmd = 1;
    cg_range_inst.sample();  // hi_range x write
    `checkr(cg_range_inst.get_inst_coverage(), 75.0);  // 6/8
    addr = 1;
    cmd = 1;
    cg_range_inst.sample();  // lo_range x write
    `checkr(cg_range_inst.get_inst_coverage(), 87.5);  // 7/8
    addr = 3;
    cmd = 0;
    cg_range_inst.sample();  // hi_range x read
    `checkr(cg_range_inst.get_inst_coverage(), 100.0);  // 8/8

    // Sample cg_at_least (option.at_least in cross body; Verilator uses at_least=1 for bins)
    // cg_at_least: 2+2+4=8 bins; 2 cross bins hit (count=1, at_least effectively 1) -> 6/8=75%
    addr = 0;
    cmd = 0;
    cg_at_least_inst.sample();  // addr0 x read
    addr = 1;
    cmd = 1;
    cg_at_least_inst.sample();  // addr1 x write
    `checkr(cg_at_least_inst.get_inst_coverage(), 75.0);

    // Sample cg_goal (option.goal in cross body; does not affect hit counting)
    // cg_goal: 2+2+4=8 bins; 2 cross bins hit -> 6/8=75%
    addr = 0;
    cmd = 0;
    cg_goal_inst.sample();  // addr0 x read
    addr = 1;
    cmd = 1;
    cg_goal_inst.sample();  // addr1 x write
    `checkr(cg_goal_inst.get_inst_coverage(), 75.0);

    // Sample cg_unsup_cross_opt
    // cg_unsup_cross_opt: 2+2+4=8 bins; 2 cross bins hit -> 6/8=75%
    addr = 0;
    cmd = 0;
    cg_unsup_cross_opt_inst.sample();  // addr0 x read
    addr = 1;
    cmd = 1;
    cg_unsup_cross_opt_inst.sample();  // addr1 x write
    `checkr(cg_unsup_cross_opt_inst.get_inst_coverage(), 75.0);

    // Sample cg_unnamed_cross
    // cg_unnamed_cross: 2+2+4=8 bins; 2 cross bins hit -> 6/8=75%
    addr = 0;
    cmd = 0;
    cg_unnamed_cross_inst.sample();  // a0 x read
    addr = 1;
    cmd = 1;
    cg_unnamed_cross_inst.sample();  // a1 x write
    `checkr(cg_unnamed_cross_inst.get_inst_coverage(), 75.0);

    // Sample cg_mixed: 10 bins total (cp_addr 2 + cp_cmd 2 + cp_solo 2 + cross ab 4)
    addr = 0; cmd = 0; mode = 0;
    cg_mixed_inst.sample();  // addr0, read, solo normal, ab(addr0_x_read)
    `checkr(cg_mixed_inst.get_inst_coverage(), 40.0);  // 4/10
    addr = 0; cmd = 1; mode = 1;
    cg_mixed_inst.sample();  // addr0, write, solo debug, ab(addr0_x_write)
    addr = 1; cmd = 0; mode = 0;
    cg_mixed_inst.sample();  // addr1, read, ab(addr1_x_read)
    addr = 1; cmd = 1; mode = 1;
    cg_mixed_inst.sample();  // addr1, write, ab(addr1_x_write)
    `checkr(cg_mixed_inst.get_inst_coverage(), 100.0);  // 10/10

    // Sample cg_def_cross (default bin in a crossed coverpoint, gated by iff)
    mode = 1;
    addr = 0; cmd = 0; cg_def_cross_inst.sample();  // a0, read
    addr = 2; cmd = 1; cg_def_cross_inst.sample();  // ad (default), write

    // Sample cg_arr_range: array range bin {[0:1]} -> av[0]=0, av[1]=1; cross 2x2
    // cg_arr_range: 2+2+4=8 bins; sample all combinations -> 100%
    addr = 0; cmd = 0; cg_arr_range_inst.sample();  // av[0] x read
    addr = 0; cmd = 1; cg_arr_range_inst.sample();  // av[0] x write
    addr = 1; cmd = 0; cg_arr_range_inst.sample();  // av[1] x read
    addr = 1; cmd = 1; cg_arr_range_inst.sample();  // av[1] x write
    `checkr(cg_arr_range_inst.get_inst_coverage(), 100.0);  // 8/8

    // Sample cg_arr_vals: array value bin {0,2} -> av[0]=0, av[1]=2; cross 2x2
    // cg_arr_vals: 2+2+4=8 bins; sample all combinations -> 100%
    addr = 0; cmd = 0; cg_arr_vals_inst.sample();  // av[0] x read
    addr = 0; cmd = 1; cg_arr_vals_inst.sample();  // av[0] x write
    addr = 2; cmd = 0; cg_arr_vals_inst.sample();  // av[1] x read
    addr = 2; cmd = 1; cg_arr_vals_inst.sample();  // av[1] x write
    `checkr(cg_arr_vals_inst.get_inst_coverage(), 100.0);  // 8/8

    // Sample cg_wild_arr: wildcard array {2'b0?} matches addr 0,1; cross 2x2
    // cg_wild_arr: 2+2+4=8 bins; sample all combinations -> 100%
    addr = 0; cmd = 0; cg_wild_arr_inst.sample();
    addr = 0; cmd = 1; cg_wild_arr_inst.sample();
    addr = 1; cmd = 0; cg_wild_arr_inst.sample();
    addr = 1; cmd = 1; cg_wild_arr_inst.sample();
    `checkr(cg_wild_arr_inst.get_inst_coverage(), 100.0);  // 8/8

    // Sample cg_wild_solo: single wildcard bin {2'b0?} matches addr 0,1; cross 1x2
    // cg_wild_solo: 1+2+2=5 bins; sample both cmd values -> 100%
    addr = 0; cmd = 0; cg_wild_solo_inst.sample();
    addr = 0; cmd = 1; cg_wild_solo_inst.sample();
    `checkr(cg_wild_solo_inst.get_inst_coverage(), 100.0);  // 5/5

    // Sample cg_arr_4state: 4-state literal bin {2'b0x} matches addr=0 (2-state sim); cross 1x2
    // cg_arr_4state: 1+2+2=5 bins; sample both cmd values -> 100%
    addr = 0; cmd = 0; cg_arr_4state_inst.sample();
    addr = 0; cmd = 1; cg_arr_4state_inst.sample();
    `checkr(cg_arr_4state_inst.get_inst_coverage(), 100.0);  // 5/5

    // Sample cg_overlap: overlapping range bins lo={0,1}, hi={1,2}; cross 2x2
    // cg_overlap: 2+2+4=8 bins; cover lo/hi via addr 0 and 2, plus addr=1 double-hits both
    addr = 0; cmd = 0; cg_overlap_inst.sample();  // lo x read
    addr = 0; cmd = 1; cg_overlap_inst.sample();  // lo x write
    addr = 2; cmd = 0; cg_overlap_inst.sample();  // hi x read
    addr = 2; cmd = 1; cg_overlap_inst.sample();  // hi x write
    addr = 1; cmd = 0; cg_overlap_inst.sample();  // addr=1 in both lo and hi (hit-list bound 2)
    `checkr(cg_overlap_inst.get_inst_coverage(), 100.0);  // 8/8

    // Sample cg_wide: 64-bit coverpoint, lo={0,1}, hi={2,3}; cross 2x2
    // cg_wide: 2+2+4=8 bins; sample all combinations -> 100%
    wide = 0; cmd = 0; cg_wide_inst.sample();  // lo x read
    wide = 0; cmd = 1; cg_wide_inst.sample();  // lo x write
    wide = 2; cmd = 0; cg_wide_inst.sample();  // hi x read
    wide = 2; cmd = 1; cg_wide_inst.sample();  // hi x write
    `checkr(cg_wide_inst.get_inst_coverage(), 100.0);  // 8/8

    // Sample cg_openrange: lo=[$:1] matches 0,1; hi=[2:$] matches 2,3; cross 2x2
    // cg_openrange: 2+2+4=8 bins; sample all combinations -> 100%
    addr = 0; cmd = 0; cg_openrange_inst.sample();  // lo x read
    addr = 0; cmd = 1; cg_openrange_inst.sample();  // lo x write
    addr = 2; cmd = 0; cg_openrange_inst.sample();  // hi x read
    addr = 2; cmd = 1; cg_openrange_inst.sample();  // hi x write
    `checkr(cg_openrange_inst.get_inst_coverage(), 100.0);  // 8/8

    // Sample cg_inv: inverted range bin never matches; only cmd bins are hittable
    // cg_inv: 1+2+2=5 bins; inv and its 2 cross bins never hit -> 2/5=40%
    addr = 0; cmd = 0; cg_inv_inst.sample();  // read
    addr = 1; cmd = 1; cg_inv_inst.sample();  // write
    `checkr(cg_inv_inst.get_inst_coverage(), 40.0);  // 2/5: read + write only

    // Sample cg_noNormal: coverpoint has no Normal bins; cross product is empty
    // cg_noNormal: 0+2+0=2 bins (cmd only); both hit -> 100%
    addr = 0; cmd = 0; cg_noNormal_inst.sample();  // read
    addr = 1; cmd = 1; cg_noNormal_inst.sample();  // write
    `checkr(cg_noNormal_inst.get_inst_coverage(), 100.0);  // 2/2

    // Sample cg_trans: transition coverpoint crossed with a value coverpoint
    // cg_trans: 1+2+2=5 bins; t01_x_v6 never completes -> 4/5=80%
    // __Vprev_cp_t initializes to 0.
    state = 0; val = 5; cg_trans_inst.sample();  // prev=0,cur=0: no t01; v5
    state = 1; val = 5; cg_trans_inst.sample();  // prev=0,cur=1: t01 completes; t01_x_v5
    state = 0; val = 6; cg_trans_inst.sample();  // prev=1,cur=0: no t01; v6 (no cross)
    `checkr(cg_trans_inst.get_inst_coverage(), 80.0);  // 4/5: t01_x_v6 not hit

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
