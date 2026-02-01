// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (
    input clk
);

  integer i;
  reg [94:0] w95;
  reg [399:0] w400;

  integer cyc = 0;

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d\n", $time, cyc);
`endif
    cyc <= cyc + 1;
    if (cyc == 0) begin
      // Setup
      w95 = {95{1'b1}};
      w400 = '1;
    end
    else if (cyc == 1) begin
      if (w95++ != {95{1'b1}}) $stop;
      if (w95 != {95{1'b0}}) $stop;
      if (w95-- != {95{1'b0}}) $stop;
      if (w95 != {95{1'b1}}) $stop;
      if (++w95 != {95{1'b0}}) $stop;
      if (w95 != {95{1'b0}}) $stop;
      if (--w95 != {95{1'b1}}) $stop;
      if (w95 != {95{1'b1}}) $stop;

      if (w400++ != {400{1'b1}}) $stop;
      if (w400 != {400{1'b0}}) $stop;
      if (w400-- != {400{1'b0}}) $stop;
      if (w400 != {400{1'b1}}) $stop;
      if (++w400 != {400{1'b0}}) $stop;
      if (w400 != {400{1'b0}}) $stop;
      if (--w400 != {400{1'b1}}) $stop;
      if (w400 != {400{1'b1}}) $stop;
    end
    else if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
