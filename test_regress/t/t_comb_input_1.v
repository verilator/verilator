// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2022 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


module top(
  clk,
  inc
);

  input clk;
  input [31:0] inc;

  // Cycle count
  reg [31:0] cyc = 0;

  /* verilator lint_off UNOPTFLAT */
  // Circular combinational logic driven from primary input. 'msb' is the
  // narrowest, so it will be the cut vertex.
  wire [31:0] feedback;
  wire [31:0] sum = cyc + inc + feedback;
  wire msb = sum[31];  // Always 0, but Verilator cannot know that
  assign feedback = {32{msb}};

  always @(posedge clk) begin
    $display("cyc: %d sum: %d", cyc, sum);
    if (sum != 2*cyc + 1) $stop;
    cyc <= cyc + 1;
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
