// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%s exp=%s\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;

  typedef struct {int x;} struct_t;

  struct_t s_array[3000];
  bit big_array[40][40][40];
  string string_array[2];
  struct_t my_struct;

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      string_array[0] = "abcd";
      big_array[1][2][3] <= 1;
      s_array[1].x <= 1;
      my_struct.x <= 1;
    end
    else if (cyc == 1) begin
      `checks(string_array[0], "abcd");
      `checkh(big_array[1][2][3], 1);
      `checkh(s_array[1].x, 1);
      `checkh(my_struct.x, 1);
    end
    else if (cyc == 2) begin
      force string_array[0] = "efgh";
      force big_array[1][2][3] = 0;
      force s_array[1].x = 0;
      force my_struct.x = 0;
    end
    else if (cyc == 3) begin
      `checks(string_array[0], "efgh");
      `checkh(big_array[1][2][3], 0);
      string_array[0] = "ijkl";
      big_array[1][2][3] <= 1;
      `checkh(s_array[1].x, 0);
      s_array[1].x <= 1;
      `checkh(my_struct.x, 0);
      my_struct.x <= 1;
    end
    else if (cyc == 4) begin
      `checks(string_array[0], "efgh");
      `checkh(big_array[1][2][3], 0);
      `checkh(s_array[1].x, 0);
      `checkh(my_struct.x, 0);
    end
    else if (cyc == 5) begin
      release string_array[0];
      release big_array[1][2][3];
      release s_array[1].x;
      release my_struct.x;
    end
    else if (cyc == 6) begin
      `checks(string_array[0], "efgh");
      `checkh(big_array[1][2][3], 0);
      string_array[0] = "mnop";
      big_array[1][2][3] <= 1;
      `checkh(s_array[1].x, 0);
      s_array[1].x <= 1;
      `checkh(my_struct.x, 0);
      my_struct.x <= 1;
    end
    else if (cyc == 7) begin
      `checks(string_array[0], "mnop");
      `checkh(big_array[1][2][3], 1);
      `checkh(s_array[1].x, 1);
      `checkh(my_struct.x, 1);
    end
    else if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
