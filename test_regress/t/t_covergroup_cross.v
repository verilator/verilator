// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test cross coverage: 2-way, 3-way, and 4-way crosses

module t;
  logic [1:0] addr;
  logic cmd;
  logic mode;
  logic parity;

  // 2-way cross
  covergroup cg2;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    addr_cmd: cross cp_addr, cp_cmd;
  endgroup

  // 3-way cross
  covergroup cg3;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
      bins addr2 = {2};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    cp_mode: coverpoint mode {
      bins normal = {0};
      bins debug  = {1};
    }
    addr_cmd_mode: cross cp_addr, cp_cmd, cp_mode;
  endgroup

  // 4-way cross
  covergroup cg4;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    cp_mode: coverpoint mode {
      bins normal = {0};
      bins debug  = {1};
    }
    cp_parity: coverpoint parity {
      bins even = {0};
      bins odd  = {1};
    }
    addr_cmd_mode_parity: cross cp_addr, cp_cmd, cp_mode, cp_parity;
  endgroup

  // Cross with option set inside the cross body
  covergroup cg5;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    addr_cmd_opt: cross cp_addr, cp_cmd {
      option.weight = 2;
    }
  endgroup

  // 2-way cross where one coverpoint uses a range bin
  covergroup cg_range;
    cp_addr: coverpoint addr {
      bins lo_range = {[0:1]};  // range bin
      bins hi_range = {[2:3]};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    addr_cmd_range: cross cp_addr, cp_cmd;
  endgroup

  // Cross where one coverpoint has ignore_bins — ignored values must not appear in cross bins
  covergroup cg_ignore;
    cp_addr: coverpoint addr {
      ignore_bins ign = {3};  // addr=3 excluded from cross
      bins a0 = {0};
      bins a1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    cross_ab: cross cp_addr, cp_cmd;
  endgroup

  // Cross with option.at_least set in the cross body
  covergroup cg_at_least;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    addr_cmd_al: cross cp_addr, cp_cmd {
      option.at_least = 3;
    }
  endgroup

  // Cross with option.goal set in the cross body
  covergroup cg_goal;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    addr_cmd_goal: cross cp_addr, cp_cmd {
      option.goal = 90;
    }
  endgroup

  // Cross with an unsupported option (option.per_instance) — Verilator warns and ignores it
  covergroup cg_unsup_cross_opt;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    addr_cmd_unsup: cross cp_addr, cp_cmd {
      option.per_instance = 1;  // unsupported for cross — expect COVERIGN warning
    }
  endgroup

  // Covergroup with an unnamed cross — the cross is reported under the default name "cross"
  covergroup cg_unnamed_cross;
    cp_a: coverpoint addr { bins a0 = {0}; bins a1 = {1}; }
    cp_c: coverpoint cmd  { bins read = {0}; bins write = {1}; }
    cross cp_a, cp_c;  // no label: reported under the default cross name
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

  initial begin
    // Sample 2-way: hit all 4 combinations
    addr = 0; cmd = 0; mode = 0; parity = 0; cg2_inst.sample();  // addr0 x read
    addr = 1; cmd = 1; mode = 0; parity = 0; cg2_inst.sample();  // addr1 x write
    addr = 0; cmd = 1; mode = 0; parity = 0; cg2_inst.sample();  // addr0 x write
    addr = 1; cmd = 0; mode = 0; parity = 0; cg2_inst.sample();  // addr1 x read

    // Sample 3-way: hit 4 of 12 combinations
    addr = 0; cmd = 0; mode = 0; cg3_inst.sample();  // addr0 x read x normal
    addr = 1; cmd = 1; mode = 0; cg3_inst.sample();  // addr1 x write x normal
    addr = 2; cmd = 0; mode = 1; cg3_inst.sample();  // addr2 x read x debug
    addr = 0; cmd = 1; mode = 1; cg3_inst.sample();  // addr0 x write x debug

    // Sample 4-way: hit 4 of 16 combinations
    addr = 0; cmd = 0; mode = 0; parity = 0; cg4_inst.sample();
    addr = 1; cmd = 1; mode = 0; parity = 1; cg4_inst.sample();
    addr = 0; cmd = 1; mode = 1; parity = 0; cg4_inst.sample();
    addr = 1; cmd = 0; mode = 1; parity = 1; cg4_inst.sample();

    // Sample cg5 (cross with option)
    addr = 0; cmd = 0; cg5_inst.sample();
    addr = 1; cmd = 1; cg5_inst.sample();

    // Sample cg_ignore: addr=3 is in ignore_bins so no cross bins for it
    addr = 0; cmd = 0; cg_ignore_inst.sample();  // a0 x read
    addr = 1; cmd = 1; cg_ignore_inst.sample();  // a1 x write
    addr = 0; cmd = 1; cg_ignore_inst.sample();  // a0 x write
    addr = 1; cmd = 0; cg_ignore_inst.sample();  // a1 x read
    addr = 3; cmd = 0; cg_ignore_inst.sample();  // ignored (addr=3 in ignore_bins)

    // Sample range-bin cross
    addr = 0; cmd = 0; cg_range_inst.sample();  // lo_range x read
    addr = 2; cmd = 1; cg_range_inst.sample();  // hi_range x write
    addr = 1; cmd = 1; cg_range_inst.sample();  // lo_range x write
    addr = 3; cmd = 0; cg_range_inst.sample();  // hi_range x read

    // Sample cg_at_least (option.at_least in cross body)
    addr = 0; cmd = 0; cg_at_least_inst.sample();  // addr0 x read
    addr = 1; cmd = 1; cg_at_least_inst.sample();  // addr1 x write

    // Sample cg_goal (option.goal in cross body)
    addr = 0; cmd = 0; cg_goal_inst.sample();  // addr0 x read
    addr = 1; cmd = 1; cg_goal_inst.sample();  // addr1 x write

    // Sample cg_unsup_cross_opt
    addr = 0; cmd = 0; cg_unsup_cross_opt_inst.sample();  // addr0 x read
    addr = 1; cmd = 1; cg_unsup_cross_opt_inst.sample();  // addr1 x write

    // Sample cg_unnamed_cross
    addr = 0; cmd = 0; cg_unnamed_cross_inst.sample();  // a0 x read
    addr = 1; cmd = 1; cg_unnamed_cross_inst.sample();  // a1 x write

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
