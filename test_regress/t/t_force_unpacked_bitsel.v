// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

`define checkh(g,e) do if ((g) !==(e)) begin $write("%%Error: %s:%0d: got=%b exp=%b\n", `__FILE__,`__LINE__, (g),(e)); $stop; end while(0)


module t (
    input clk
);
  int cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;

  logic [3:0] var_arr [2];

  always @(posedge clk) begin
    var_arr[0] <= 4'b0101;
    var_arr[1] <= (cyc <= 3) ? 4'b1111 : (cyc <= 7) ? 4'b0000 : 4'b0001;
  end

  always @(posedge clk) begin
    if (cyc == 2) force var_arr[1][0] = 1'b0;
    if (cyc == 6) force var_arr[1][3] = 1'b1;
    if (cyc == 8) release var_arr[1][0];
    if (cyc == 10) force var_arr[1] = 4'b1010;
    if (cyc == 12) release var_arr[1];
  end

  always @(posedge clk) case (cyc)
    1: begin
      `checkh(var_arr[0], 4'b0101);
      `checkh(var_arr[1], 4'b1111);
    end
    3: begin
      `checkh(var_arr[1], 4'b1110);
    end
    5: begin
      `checkh(var_arr[1], 4'b0000);
    end
    7: begin
      `checkh(var_arr[1], 4'b1000);
    end
    9: begin
      `checkh(var_arr[1], 4'b1001);
    end
    11: begin
      `checkh(var_arr[1], 4'b1010);
      `checkh(var_arr[0], 4'b0101);
    end
    13: begin
      `checkh(var_arr[1], 4'b0001);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  endcase
endmodule
