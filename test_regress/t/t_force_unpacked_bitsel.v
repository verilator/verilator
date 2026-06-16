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

  logic [4:1] var_arr [2];
  /* verilator lint_off ASCRANGE */
  logic [1:4] var_arr_a [2];
  /* verilator lint_on ASCRANGE */
  logic [72:1] wide_arr [2];

  always @(posedge clk) begin
    var_arr[0] <= 4'b0101;
    var_arr[1] <= (cyc <= 3) ? 4'b1111 : (cyc <= 7) ? 4'b0000 : 4'b0001;
    var_arr_a[0] <= 4'b1010;
    var_arr_a[1] <= 4'b0000;
    wide_arr[0] <= '0;
    wide_arr[1] <= 72'hAB_CDEF0123_456789AB;
  end

  always @(posedge clk) begin
    if (cyc == 2) force var_arr[1][1] = 1'b0;
    if (cyc == 6) force var_arr[1][4] = 1'b1;
    if (cyc == 8) release var_arr[1][1];
    if (cyc == 10) force var_arr[1] = 4'b1010;
    if (cyc == 12) release var_arr[1];

    if (cyc == 2) force wide_arr[1][36:5] = 32'hffff_ffff;
    if (cyc == 4) release wide_arr[1];

    if (cyc == 2) force var_arr_a[1][2:4] = 3'b111;
    if (cyc == 4) force var_arr_a[1][3]= 1'b0;
    if (cyc == 6) release var_arr_a[1];
    if (cyc == 7) force var_arr_a[1][3:4] = 2'b11;
    if (cyc == 9) force var_arr_a[1][2:3]= 2'b00;
    if (cyc == 11) release var_arr_a[1];
    if (cyc == 12) force var_arr_a[1][1:2] = 2'b11;
    if (cyc == 14) force var_arr_a[1][2:3]= 2'b00;
    if (cyc == 16) release var_arr_a[1];
    if (cyc == 17) force var_arr_a[1][2:3] = 2'b11;
    if (cyc == 19) force var_arr_a[1][1:3]= 3'b000;
    if (cyc == 21) release var_arr_a[1];

    if (cyc == 14) force var_arr[1][1] = 1'b0;
    if (cyc == 14) force var_arr[0][1] = 1'b0;
    if (cyc == 16) release var_arr[1][1];
    if (cyc == 16) release var_arr[0][1];
    if (cyc == 18) force var_arr[0] = 4'b1010;
    if (cyc == 20) force var_arr[0][1] = 1'b1;
    if (cyc == 22) release var_arr[0];
  end

  always @(posedge clk) case (cyc)
    1: begin
      `checkh(var_arr[0], 4'b0101);
      `checkh(var_arr[1], 4'b1111);
    end
    3: begin
      `checkh(var_arr[1], 4'b1110);
      `checkh(wide_arr[1][36:5], 32'hffff_ffff);
      `checkh(wide_arr[1][4:1], 4'hB);
      `checkh(wide_arr[1][72:37], 36'hABCDEF012);
      `checkh(var_arr_a[1], 4'b0111);
      `checkh(var_arr_a[0], 4'b1010);
    end
    5: begin
      `checkh(var_arr[1], 4'b0000);
      `checkh(wide_arr[1], 72'hAB_CDEF0123_456789AB);
      `checkh(var_arr_a[1], 4'b0101);
    end
    7: begin
      `checkh(var_arr[1], 4'b1000);
    end
    8: begin
      `checkh(var_arr_a[1], 4'b0011);
    end
    9: begin
      `checkh(var_arr[1], 4'b1001);
    end
    10: begin
      `checkh(var_arr_a[1], 4'b0001);
    end
    11: begin
      `checkh(var_arr[1], 4'b1010);
      `checkh(var_arr[0], 4'b0101);
    end
    13: begin
      `checkh(var_arr[1], 4'b0001);
      `checkh(var_arr_a[1], 4'b1100);
    end
    15: begin
      `checkh(var_arr_a[1], 4'b1000);
      `checkh(var_arr[1], 4'b0000);
      `checkh(var_arr[0], 4'b0100);
    end
    17: begin
      `checkh(var_arr[1], 4'b0001);
      `checkh(var_arr[0], 4'b0101);
    end
    18: begin
      `checkh(var_arr_a[1], 4'b0110);
    end
    19: begin
      `checkh(var_arr[0], 4'b1010);
    end
    20: begin
      `checkh(var_arr_a[1], 4'b0000);
    end
    21: begin
      `checkh(var_arr[0], 4'b1011);
    end
    22: begin
      `checkh(var_arr_a[1], 4'b0000);
    end
    23: begin
      `checkh(var_arr[0], 4'b0101);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  endcase
endmodule
