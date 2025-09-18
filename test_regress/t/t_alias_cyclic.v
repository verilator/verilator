// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional transitive alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  wire [31:0] a = 32'hdeadbeef;
  wire [31:0] b;

  alias a = b;
  alias a = b;
//  alias b = a;
//  alias a = a;

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("a = %x, b = %x\n", a, b);
`endif
    if (b != 32'hdeadbeef) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
