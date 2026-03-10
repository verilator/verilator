// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  logic [1:0] data;

  // Covergroup with 4 bins
  covergroup cg @(posedge clk);
    cp: coverpoint data {
      bins low  = {2'b00};
      bins mid1 = {2'b01};
      bins mid2 = {2'b10};
      bins high = {2'b11};
    }
  endgroup

  cg cg_inst = new;

  initial begin
    // Initially no bins covered - should be 0%
    real cov;
    cov = cg_inst.get_inst_coverage();
    $display("Coverage after 0 samples: %f", cov);
    `checkr(cov, 0.0);

    // Cover 1 bin (low) - should be 25%
    @(posedge clk);
    data = 2'b00;
    @(posedge clk);
    cov = cg_inst.get_inst_coverage();
    $display("Coverage after 1/4 bins: %f", cov);
    `checkr(cov, 25.0);

    // Cover 2nd bin (mid1) - should be 50%
    @(posedge clk);
    data = 2'b01;
    @(posedge clk);
    cov = cg_inst.get_inst_coverage();
    $display("Coverage after 2/4 bins: %f", cov);
    `checkr(cov, 50.0);

    // Cover 3rd bin (mid2) - should be 75%
    @(posedge clk);
    data = 2'b10;
    @(posedge clk);
    cov = cg_inst.get_inst_coverage();
    $display("Coverage after 3/4 bins: %f", cov);
    `checkr(cov, 75.0);

    // Cover 4th bin (high) - should be 100%
    @(posedge clk);
    data = 2'b11;
    @(posedge clk);
    cov = cg_inst.get_inst_coverage();
    $display("Coverage after 4/4 bins: %f", cov);
    `checkr(cov, 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
