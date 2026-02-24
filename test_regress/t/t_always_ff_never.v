// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface intf (
    input wire clk  /*verilator public*/
);
endinterface

module sub (
    input wire clk,
    input wire dat
);
  intf the_intf (.clk);

  logic [63:0] last_transition = 123;
  always_ff @(edge dat) begin
    last_transition <= $time;
  end

  int cyc = 0;
  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) begin
      if (last_transition != 123) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module t (
    input clk
);

  sub the_sub (
      .clk,
      .dat('0)
  );
endmodule
