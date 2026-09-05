// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(g,e) do if ((g) !==(e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)

`ifdef CMT
 `define FORCEABLE /*verilator forceable*/
`else
 `define FORCEABLE
`endif
// verilog_format: on

module t (input wire clk, output reg [31:0] cyc);
  initial cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;

  reg [4:3] var_arr [7:6][5:4] `FORCEABLE;
  //verilator lint_off ASCRANGE
  reg [3:4] var_arr_a [6:7][4:5] `FORCEABLE;

  initial begin
    var_arr[6][4]   = 2'h1; var_arr[6][5]   = 2'h2;
    var_arr[7][4]   = 2'h3; var_arr[7][5]   = 2'h2;
    var_arr_a[6][4] = 2'h2; var_arr_a[6][5] = 2'h1;
    var_arr_a[7][4] = 2'h1; var_arr_a[7][5] = 2'h3;
  end

  always @(posedge clk) case (cyc)
    0: begin
      `checkh(var_arr[6][4],   2'h1);
      `checkh(var_arr[6][5],   2'h2);
      `checkh(var_arr[7][4],   2'h3);
      `checkh(var_arr[7][5],   2'h2);
      `checkh(var_arr_a[6][4], 2'h2);
      `checkh(var_arr_a[6][5], 2'h1);
      `checkh(var_arr_a[7][4], 2'h1);
      `checkh(var_arr_a[7][5], 2'h3);
    end
    1: begin
      `checkh(var_arr[6][5],   2'h3);
      `checkh(var_arr_a[6][5], 2'h2);
      `checkh(var_arr[6][4],   2'h1);
      `checkh(var_arr[7][4],   2'h3);
      `checkh(var_arr_a[6][4], 2'h2);
      `checkh(var_arr_a[7][4], 2'h1);
    end
    2: begin
      `checkh(var_arr[6][5],   2'h3);
      `checkh(var_arr[7][4],   2'h2);
      `checkh(var_arr_a[6][5], 2'h2);
      `checkh(var_arr_a[7][4], 2'h3);
    end
    3: begin
      `checkh(var_arr[6][5],   2'h2);
      `checkh(var_arr[7][4],   2'h2);
      `checkh(var_arr_a[6][5], 2'h1);
      `checkh(var_arr_a[7][4], 2'h3);
    end
    4: begin
      `checkh(var_arr[6][4],   2'h1);
      `checkh(var_arr[6][5],   2'h2);
      `checkh(var_arr[7][4],   2'h3);
      `checkh(var_arr[7][5],   2'h2);
      `checkh(var_arr_a[6][4], 2'h2);
      `checkh(var_arr_a[6][5], 2'h1);
      `checkh(var_arr_a[7][4], 2'h1);
      `checkh(var_arr_a[7][5], 2'h3);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  endcase
endmodule
