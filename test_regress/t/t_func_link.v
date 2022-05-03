// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module Test(/*AUTOARG*/
  // Outputs
  out,
  // Inputs
  clk, in
  );

  // Replace this module with the device under test.
  //
  // Change the code in the t module to apply values to the inputs and
  // merge the output values into the result vector.

  input clk;
  input [31:0] in;
  output reg [31:0] out;
  integer cyc = 0;

  SubTest subtest(.out);

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d\n", $time, cyc);
`endif
    cyc <= cyc + 1;
    if (cyc < 99) begin
      subtest.block.set(in);
    end
    else begin
      $write("[%0t] cyc==%0d\n", $time, cyc);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module SubTest(
  output logic[31:0] out
);

  if (1) begin : block

  function void set(logic[31:0] in);
    out <= in;
  endfunction

  end : block

endmodule
