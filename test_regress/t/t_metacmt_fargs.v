// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator fargs --binary -Wno-WIDTHEXPAND
/* verilator fargs -Wno-WIDTHTRUNC */  /* verilator fargs --trace-vcd --stats */

module top;

  bit clk = 0;
  always #5 clk = ~clk;
  reg [3:0] cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 10'd1;  // Intentional width warning
    $display("%8t %1d", $time, cyc);
    if (cyc == 3'd7) begin  // Intentional width warning
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
