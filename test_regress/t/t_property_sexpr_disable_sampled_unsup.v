// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%p exp='h%p\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;

  localparam MAX = 10;
  int cyc = 0;
  int passes = 0;
  int fails = 0;

  assert property (@(posedge clk) disable iff ($sampled(cyc) == 4) 1 ##1 cyc % 3 == 0) passes++;
  else fails++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == MAX) begin
      `checkh(passes, 3);
      `checkh(fails, 4);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
