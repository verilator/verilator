// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t(clk);
  input clk;

  typedef struct {
    int x;
  } struct_t;

  int cyc = 0;
  struct_t array[1];
  int res = 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) begin
      array[0].x <= 1;
    end
    if (cyc == 2) begin
      array[0].x = 0;
    end
    if (cyc == 3) begin
      if (res != 0) $stop;
      $finish;
    end
  end

  always @(array[0].x) res = array[0].x;
endmodule
