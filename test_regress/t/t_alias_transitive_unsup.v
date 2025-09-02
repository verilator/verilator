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
  wire [31:0] c;

  transfer transfer_i (
      .a(a),
      .b(b),
      .c(c)
  );

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("a = %x, b = %x, c = %x\n", a, b, c);
`endif
    if (c != 32'hdeadbeef) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module transfer (
    inout wire [31:0] a,
    inout wire [31:0] b,
    inout wire [31:0] c
);

  alias a = b = c;

endmodule
