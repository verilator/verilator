// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  int pass_count[6];

  property named_s_until;
    @(posedge clk) (cyc == 1) |=> 1'b1 s_until (cyc == 3);
  endproperty

`ifdef TEST_PRE_NOTIMING
  property named_bare_s_until;
    @(posedge clk) 1'b1 s_until 1'b1;
  endproperty

  assert property (named_bare_s_until);
`endif

`ifdef TEST_WIDTH_NOTIMING
  assert property (@(posedge clk) 1'b1 s_until 1'b1);
`endif

  // These obligations resolve normally and must not fail at end of simulation.
  assert property (named_s_until) pass_count[0]++;
  assert property (@(posedge clk) (cyc == 1) |=> 1'b1 s_until (cyc == 3)) pass_count[1]++;
  assert property (@(posedge clk) (cyc == 1) |=> 1'b1 s_until_with (cyc == 3)) pass_count[2]++;
  assert property (@(posedge clk) (cyc == 0) |-> ##1 (1'b1 s_until (cyc == 2))) pass_count[3]++;
  assert property (@(posedge clk) ##1 (1'b0 s_until 1'b1)) pass_count[4]++;
  assert property (@(posedge clk) ##1 (1'b1 s_until_with 1'b1)) pass_count[5]++;
  cover property (@(posedge clk) (cyc == 1) |=> 1'b1 s_until 1'b0);

  // This obligation remains live and must fail at end of simulation.
  assert property (@(posedge clk) (cyc == 1) |=> 1'b1 s_until 1'b0);

  final begin
    `checkd(pass_count[0], 5);
    `checkd(pass_count[1], 5);
    `checkd(pass_count[2], 5);
    `checkd(pass_count[3], 5);
    `checkd(pass_count[4], 4);
    `checkd(pass_count[5], 4);
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end

endmodule
