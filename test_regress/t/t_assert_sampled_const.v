// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
  input logic clk
);

  localparam OP_UNTYPED = 3'b000;
  localparam logic [2:0] OP_LOGIC = 3'b011;
  localparam logic [2:0] OP_WILD = 3'b1x1;

  logic [4:0] cyc = 0;
  logic [2:0] opcode;

  int hit_untyped = 0;
  int hit_logic = 0;
  int hit_wild = 0;

  always @(posedge clk) if (cyc != 5'd31) cyc <= cyc + 1;

  assign opcode = (cyc < 16) ? cyc[2:0] : 3'b010;

  assert property (@(posedge clk) opcode inside {OP_UNTYPED}) hit_untyped++;
  assert property (@(posedge clk) opcode inside {OP_LOGIC}) hit_logic++;
  assert property (@(posedge clk) opcode ==? OP_WILD) hit_wild++;

  always @(posedge clk) begin
    if (cyc == 24) begin
      `checkd(hit_untyped, 2);
      `checkd(hit_logic, 2);
      `checkd(hit_wild, 4);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
