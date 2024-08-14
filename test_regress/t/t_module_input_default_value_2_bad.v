// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Andrew Ranck
// SPDX-License-Identifier: CC0-1.0

// Test for Issue#5358: Support default value on module input.
// This test *is* expected to not compile, and must match .out file.


module dut_should_fail_compile2
  (
   input logic  i = 1'b1,
   output logic o
   );
  always_comb begin
    i = 1'b0; // bad, should fail post link in V3Width
  end
  assign o = i;
endmodule



module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

  input clk;
  int   cyc = 0;

  // 1800-2009, a few flavors to test:
  // We should have some DUT instances that fail to compile,
  // if you tried having a default value on port output.
  logic        dut_should_fail_o;
  dut_should_fail_compile2 u_dut_should_fail_compile1
    (.i(1'b0),
     .o(dut_should_fail_o)
     );

  always @(posedge clk) begin : main
    cyc <= cyc + 1;
    if (cyc == 10) begin
      // done checking various DUTs and finish
      $display("%t %m: cyc=%0d", $time, cyc);
      $write("*-* All Finished *-*\n");
      $finish();
    end

  end

endmodule : t
