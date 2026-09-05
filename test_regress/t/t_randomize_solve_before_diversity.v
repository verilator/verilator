// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 18.5.9's worked example for solve...before: s should land
// on 0/1 with ~50/50 probability, even though d shares a constraint with it.
class SolveBeforeDiversity;
  rand bit s;
  rand bit [7:0] d;
  constraint c {
    s -> d == 0;
  }
  constraint order {
    solve s before d;
  }
endclass

module t;
  parameter int N = 8000;  // randomize() calls
  parameter int TOL_PCT = 30;  // +-% tolerance on expected count

  initial begin
    int randomize_result;
    automatic SolveBeforeDiversity obj = new();
    automatic int s_count = 0;
    repeat (N) begin
      randomize_result = obj.randomize();
      `checkd(randomize_result, 1);
      if (obj.s) begin
        `checkd(obj.d, 8'h00);
      end
      if (obj.s) s_count++;
    end
    `check_range(s_count, (N / 2) * (100 - TOL_PCT) / 100, (N / 2) * (100 + TOL_PCT) / 100);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
