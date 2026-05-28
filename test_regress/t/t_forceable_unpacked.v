// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

`define checkh(g,e) do if ((g) !==(e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); $stop; end while(0)

module t (input wire clk, output reg [31:0] cyc);
  reg [15:0] tmp;
  initial begin cyc = 0; tmp = 16'h0260; end
  always @(posedge clk) cyc <= cyc + 1;

  reg [3:0] var_arr [1:0][1:0] `ifdef CMT /*verilator forceable*/ `endif;
  always @* {var_arr[0][0], var_arr[0][1], var_arr[1][0], var_arr[1][1]} = tmp;

  always @(posedge clk) case (cyc)
    1:       force var_arr[0][0] = 4'h7;
    3:       `checkh(var_arr[0][0], 4'h7);
    4:       `checkh(var_arr[0][1], 4'ha);
    5: begin `checkh(var_arr[0][1], 4'ha); `checkh(var_arr[1][0], 4'hb); end
    6:       release var_arr[0][0];
    7: begin `checkh(var_arr[0][1], 4'h2); `checkh(var_arr[1][0], 4'hb); end
    8:       `checkh(var_arr[0][0], 4'h0);
    9: begin `checkh(var_arr[0][1], 4'h2); `checkh(var_arr[1][0], 4'h6);
             $write("*-* All Finished *-*\n"); $finish; end
  endcase
endmodule
