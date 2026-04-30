// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cnt;

  typedef struct packed {
    logic foo;
    logic bar;
  } struct_t;

  wire struct_t struct_wire;
  var struct_t struct_logic;

  assign struct_wire = '{foo: cnt[0], bar: cnt[1]};
  always @(posedge clk) struct_logic <= '{foo: ~cnt[0], bar: ~cnt[1]};

  initial cnt = 0;
  always @(posedge clk) begin
    cnt <= cnt + 1;
    if (cnt == 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
