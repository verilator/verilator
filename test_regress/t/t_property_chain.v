// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  int cyc = 0;
  int or_fails = 0;
  int goto_fails = 0;
  wire a = cyc == 2;
  wire b = cyc == 2 || cyc == 4;
  wire zero = 1'b0;

  property p_or(x, y, z);
    x |=> y || z;
  endproperty
  // The body of a property can be a property instance (IEEE 1800-2023 16.12)
  property p_or_chain(x, y, z);
    p_or(x, y, z);
  endproperty
  property p_goto(x, y);
    x [->2] |-> y;
  endproperty
  property p_goto_chain(x, y);
    p_goto(x, y);
  endproperty

  // Every attempt that fails runs the fail statement (IEEE 1800-2023 16.14.1)
  assert property (@(posedge clk) p_or_chain(a, zero, zero))
  else or_fails++;
  assert property (@(posedge clk) p_goto_chain(b, zero))
  else goto_fails++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      `checkd(or_fails, 1);
      `checkd(goto_fails, 3);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
