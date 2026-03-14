// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test 3-way cross coverage

module t;
  logic [1:0] addr;
  logic cmd;
  logic mode;

  // Covergroup with 3-way cross coverage
  covergroup cg;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
      bins addr2 = {2};
    }
    cp_cmd: coverpoint cmd {
      bins read = {0};
      bins write = {1};
    }
    cp_mode: coverpoint mode {
      bins normal = {0};
      bins debug = {1};
    }
    // 3-way cross: addr x cmd x mode = 3 x 2 x 2 = 12 cross bins
    addr_cmd_mode: cross cp_addr, cp_cmd, cp_mode;
  endgroup

  cg cg_inst = new;

  initial begin
    addr = 0; cmd = 0; mode = 0; cg_inst.sample();  // addr0 x read x normal
    addr = 1; cmd = 1; mode = 0; cg_inst.sample();  // addr1 x write x normal
    addr = 2; cmd = 0; mode = 1; cg_inst.sample();  // addr2 x read x debug
    addr = 0; cmd = 1; mode = 1; cg_inst.sample();  // addr0 x write x debug

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
