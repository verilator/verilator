// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface with_port (
    input logic [31:0] status[1]
);
endinterface

interface with_signal;
  logic x;
endinterface

module chk;
  with_signal i ();
endmodule

module block (
    input logic clk,
    output logic [31:0] status
);  /*verilator hier_block*/
  always_ff @(posedge clk) status <= status + 1'b1;
endmodule

bind block with_port with_port ('{status});
bind block chk m_blk ();

module t (
    input logic clk
);
  logic [31:0] status;

  block block (.*);
  chk u_chk ();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
