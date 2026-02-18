// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
          // Inputs
          clk
          );
  input clk;

  int cyc;
  initial cyc = 0;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  sub the_sub (.*);

endmodule

module sub_sub
(
    input  logic [4-1:0][32-1:0]   data_in
);
endmodule

module sub ();
    logic [4-1:0][32-1:0][1-1:0] some_data;
    sub_sub
    the_sub_sub (
        .data_in    (some_data)
    );
endmodule
