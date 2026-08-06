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
  int hit_sampled = 0;
  int hit_past = 0;
  int hit_past_n = 0;
  int hit_stable = 0;
  int hit_norose = 0;
  int hit_nofell = 0;
  int hit_nochanged = 0;
  int hit_wild_samp = 0;

  always @(posedge clk) if (cyc != 5'd31) cyc <= cyc + 1;

  assign opcode = (cyc < 16) ? cyc[2:0] : 3'b010;

  assert property (@(posedge clk) opcode inside {OP_UNTYPED}) hit_untyped++;
  assert property (@(posedge clk) opcode inside {OP_LOGIC}) hit_logic++;
  assert property (@(posedge clk) opcode ==? OP_WILD) hit_wild++;

  assert property (@(posedge clk) $sampled(OP_LOGIC) == OP_LOGIC) hit_sampled++;
  assert property (@(posedge clk) $past(OP_LOGIC) == OP_LOGIC) hit_past++;
  assert property (@(posedge clk) $past(OP_LOGIC, 3) == OP_LOGIC) hit_past_n++;
  assert property (@(posedge clk) $stable(OP_LOGIC)) hit_stable++;
  assert property (@(posedge clk) !$rose(OP_LOGIC)) hit_norose++;
  assert property (@(posedge clk) !$fell(OP_LOGIC)) hit_nofell++;
  assert property (@(posedge clk) !$changed(OP_LOGIC)) hit_nochanged++;

  assert property (@(posedge clk) $sampled(OP_WILD) === OP_WILD) hit_wild_samp++;

  always @(posedge clk) begin
    if (cyc == 24) begin
      `checkd(hit_untyped, 2);
      `checkd(hit_logic, 2);
      `checkd(hit_wild, 4);

      `checkd(hit_sampled, 24);
      `checkd(hit_wild_samp, 24);
      `checkd(hit_nofell, 24);

      `checkd(hit_past, 23);
      `checkd(hit_stable, 23);
      `checkd(hit_norose, 23);
      `checkd(hit_nochanged, 23);

      `checkd(hit_past_n, 21);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
