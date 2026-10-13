// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic a, b;

  int hit_fell = 0;
  int hit_rose = 0;
  int hit_stable = 0;
  int hit_changed = 0;

  default clocking cb @(posedge clk);
  endclocking

  // b changes only on even cycles; both are constant from cycle 16
  assign a = (cyc < 16) ? cyc[0] : 1'b1;
  assign b = (cyc < 16) ? cyc[1] : 1'b0;

  // Sampled value functions in the cover sequence match count
  cover sequence (a ##1 $fell(b)) hit_fell++;
  cover sequence (a ##1 $rose(b)) hit_rose++;
  cover sequence (!a ##1 $stable(b)) hit_stable++;
  cover sequence (a ##1 $changed(b)) hit_changed++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 20) $finish;
  end

  final begin
    `checkd(hit_fell, 4);  // Cycles 4, 8, 12, 16
    `checkd(hit_rose, 4);  // Cycles 2, 6, 10, 14
    `checkd(hit_stable, 8);  // Cycles 1, 3, ..., 15
    `checkd(hit_changed, hit_fell + hit_rose);
    $write("*-* All Finished *-*\n");
  end
endmodule
