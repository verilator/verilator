// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;

  typedef struct {int x;} struct_t;
  typedef union {
    int   x;
    logic y;
  } union_t;

  struct_t s_array[3000];
  bit big_array[40][40][40];
  union_t my_union;

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      big_array[1][2][3] <= 1;
      s_array[1].x <= 1;
      my_union.x <= 1;
    end else if (cyc == 1) begin
      `checkr(big_array[1][2][3], 1);
      `checkh(s_array[1].x, 1);
      `checkh(my_union.x, 1);
    end else if (cyc == 2) begin
      force big_array[1][2][3] = 0;
      force s_array[1].x = 0;
      force my_union.x = 0;
    end else if (cyc == 3) begin
      `checkr(big_array[1][2][3], 0);
      big_array[1][2][3] <= 1;
      `checkh(s_array[1].x, 0);
      s_array[1].x <= 1;
      `checkh(my_union.x, 0);
      my_union.x <= 1;
    end else if (cyc == 4) begin
      `checkr(big_array[1][2][3], 0);
      `checkh(s_array[1].x, 0);
      `checkh(my_union.x, 0);
    end else if (cyc == 5) begin
      release big_array[1][2][3];
      release s_array[1].x;
      release my_union.x;
    end else if (cyc == 6) begin
      `checkr(big_array[1][2][3], 0);
      big_array[1][2][3] <= 1;
      `checkh(s_array[1].x, 0);
      s_array[1].x <= 1;
      `checkh(my_union.x, 0);
      my_union.x <= 1;
    end else if (cyc == 7) begin
      `checkr(big_array[1][2][3], 1);
      `checkh(s_array[1].x, 1);
      `checkh(my_union.x, 1);
    end else if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
