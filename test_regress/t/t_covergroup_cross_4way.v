// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test 4-way cross coverage

module t;
  logic [1:0] addr;
  logic cmd;
  logic mode;
  logic parity;

  // Covergroup with 4-way cross coverage
  covergroup cg;
    cp_addr: coverpoint addr {
      bins addr0 = {0};
      bins addr1 = {1};
    }
    cp_cmd: coverpoint cmd {
      bins read = {0};
      bins write = {1};
    }
    cp_mode: coverpoint mode {
      bins normal = {0};
      bins debug = {1};
    }
    cp_parity: coverpoint parity {
      bins even = {0};
      bins odd = {1};
    }
    // 4-way cross: addr x cmd x mode x parity = 2 x 2 x 2 x 2 = 16 cross bins
    addr_cmd_mode_parity: cross cp_addr, cp_cmd, cp_mode, cp_parity;
  endgroup

  cg cg_inst = new;

  initial begin
    addr = 0; cmd = 0; mode = 0; parity = 0; cg_inst.sample();
    addr = 1; cmd = 1; mode = 0; parity = 1; cg_inst.sample();
    addr = 0; cmd = 1; mode = 1; parity = 0; cg_inst.sample();
    addr = 1; cmd = 0; mode = 1; parity = 1; cg_inst.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
