// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// $past in 'final' reads the correct stage for on-tick and between-tick ends

module t;

  bit clk = 0;
  bit data = 0;
  bit offedge = 0;
  int cyc = 0;

  always #1 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    data <= ~data;
    if (!offedge && cyc == 2) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  default clocking cb @(posedge clk);
  endclocking

  initial begin
    offedge = $test$plusargs("offedge") != 0;
    if (offedge) begin
      #6;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  final begin
    if ($past(data) !== (offedge ? 1'b0 : 1'b1)) begin
      $display("%%Error: wrong $past in final: got=%0b offedge=%0b", $past(data), offedge);
      $stop;
    end
  end

endmodule
