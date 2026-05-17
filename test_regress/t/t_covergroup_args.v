// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// A plain (non-covergroup) class included to verify it does not interfere with covergroup handling
class PlainClass;
    int x;
endclass

// Top-level (file-scope) covergroup declared outside any module
covergroup cg_toplevel;
  cp_tl: coverpoint 0;
endgroup

module t;

  int i, j;
  logic clk = 0;

  covergroup cg(int var1, int var2 = 42);
    cp1: coverpoint i { bins lo = {[0:4]}; bins hi = {[5:9]}; }
  endgroup

  // Clocked covergroup with constructor arguments
  covergroup cg_clocked(int lim) @(posedge clk);
    cp_clocked: coverpoint i { bins lo = {[0:4]}; bins hi = {[5:9]}; }
  endgroup

  cg cov1 = new(69, 77);
  cg cov2 = new(69);
  cg_clocked cov_clocked = new(10);
  PlainClass plain_inst = new;  // Non-covergroup class instance - must not affect covergroup coverage

  function void x();
    real cov_result;
    cov1.set_inst_name("the_inst_name");
    cov1.start();
    cov1.sample();
    cov1.stop();

    cov_result = cov2.get_coverage();
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_coverage() out of range: %f", cov_result);

    cov_result = cov2.get_coverage(i, j);
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_coverage(i,j) return out of range: %f", cov_result);

    cov_result = cov2.get_inst_coverage();
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_inst_coverage() out of range: %f", cov_result);

    cov_result = cov2.get_inst_coverage(i, j);
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_inst_coverage(i,j) return out of range: %f", cov_result);

    cov_result = cg::get_coverage();
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: cg::get_coverage() out of range: %f", cov_result);

    cov_result = cg::get_coverage(i, j);
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: cg::get_coverage(i,j) return out of range: %f", cov_result);
  endfunction

  initial begin
    i = 3;
    x();             // samples cov1 with i=3 -> lo bin hit
    clk = 1;         // posedge: samples cov_clocked with i=3 -> lo bin hit
    $finish;
  end

endmodule
