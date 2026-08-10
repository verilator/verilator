// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 1'b0;
  logic por_n = 1'b0;
  logic [31:0] sel;
  logic src_by1, src_by2, src_by4;

  logic clk_force /* verilator public */;

  always #5 clk = ~clk;
  assign src_by1 = clk;
  assign src_by2 = 1'b0;
  assign src_by4 = 1'b0;

  initial begin
    sel = 32'd1;
    void'($value$plusargs("sel=%d", sel));
  end

  initial begin
    por_n = 1'b0;
    #1 por_n = 1'b1;
  end

  always @(posedge por_n) begin
    force clk_force = (sel == 32'd1) ? src_by1 :
                      (sel == 32'd2) ? src_by2 :
                      (sel == 32'd4) ? src_by4 : src_by1;
  end

  int n_src = 0;
  int n_force = 0;
  always @(posedge src_by1) n_src++;
  always @(posedge clk_force) n_force++;

  initial begin
    #205;
    $display("n_src=%0d n_force=%0d sel=%0d", n_src, n_force, sel);

    `checkd(n_force, n_src);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule