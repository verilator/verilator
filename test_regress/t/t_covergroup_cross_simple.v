// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test basic cross coverage with 2-way cross

module t;
  logic [1:0] addr;
  logic cmd;

  covergroup cg;
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

  cg cg_inst = new;

  initial begin
    addr = 0; cmd = 0; cg_inst.sample();  // addr0 x read
    addr = 1; cmd = 1; cg_inst.sample();  // addr1 x write
    addr = 0; cmd = 1; cg_inst.sample();  // addr0 x write
    addr = 1; cmd = 0; cg_inst.sample();  // addr1 x read

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
