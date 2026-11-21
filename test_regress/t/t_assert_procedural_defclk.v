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
  bit clk2 = 0;
  int ncyc = 0;
  always @(negedge clk) ncyc <= ncyc + 1;

  default clocking @(posedge clk2);
  endclocking

  // The body reads the clock, so none is inferred and default clocking applies
  int pass_default = 0;
  int fail_default = 0;
  always @(negedge clk) begin
    if (!clk && ncyc % 10 == 2) assert property (##1 ncyc % 10 >= 4) ++pass_default;
    else ++fail_default;
  end

  // A clock inferred from the procedure supersedes default clocking
  int pass_inferred = 0;
  int fail_inferred = 0;
  always @(negedge clk) begin
    if (ncyc % 10 == 2) assert property (##1 ncyc % 10 >= 4) ++pass_inferred;
    else ++fail_inferred;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    clk2 <= ~clk2;
    if (cyc == 99) begin
      `checkd(pass_default, 10);
      `checkd(fail_default, 0);
      `checkd(pass_inferred, 0);
      `checkd(fail_inferred, 10);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
