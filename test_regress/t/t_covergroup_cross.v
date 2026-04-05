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

  // Cross with option inside body: exercises addOptionsp in visit(AstCoverCross*)
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

  // 2-way cross with range bin: exercises lo!=hi path in buildBinCondition
  covergroup cg_range;
    cp_addr: coverpoint addr {
      bins lo_range = {[0:1]};  // range bin (lo != hi) -> makeRangeCondition path
      bins hi_range = {[2:3]};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    addr_cmd_range: cross cp_addr, cp_cmd;
  endgroup

  // Cross where one coverpoint has ignore_bins: exercises BINS_USER FALSE branch
  // in collectBins during cross code generation (L1139)
  covergroup cg_ignore;
    cp_addr: coverpoint addr {
      ignore_bins ign = {3};  // BINS_IGNORE: not BINS_USER, exercises L1139 FALSE path
      bins a0 = {0};
      bins a1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read  = {0};
      bins write = {1};
    }
    cross_ab: cross cp_addr, cp_cmd;
  endgroup

  // Covergroup with unnamed cross: exercises crossName.empty() fallback to "cross" (L1395)
  covergroup cg_unnamed_cross;
    cp_a: coverpoint addr { bins a0 = {0}; bins a1 = {1}; }
    cp_c: coverpoint cmd  { bins read = {0}; bins write = {1}; }
    cross cp_a, cp_c;  // no label -> crossName is empty
  endgroup

  cg2 cg2_inst = new;
  cg_ignore cg_ignore_inst = new;
  cg_range cg_range_inst = new;
  cg3 cg3_inst = new;
  cg4 cg4_inst = new;
  cg5 cg5_inst = new;
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

    // Sample cg_unnamed_cross: exercises unnamed cross (crossName fallback to "cross")
    addr = 0; cmd = 0; cg_unnamed_cross_inst.sample();  // a0 x read
    addr = 1; cmd = 1; cg_unnamed_cross_inst.sample();  // a1 x write

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
