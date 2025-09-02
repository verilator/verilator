// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  wire [15:0] x_fwd = 16'h1234;
  wire [15:0] y_fwd;
  wire [15:0] x_bwd;
  wire [15:0] y_bwd = 16'habcd;

  sub sub_fwd_i (
      .a(x_fwd),
      .b(y_fwd)
  );
  sub sub_bwd_i (
      .a(x_bwd),
      .b(y_bwd)
  );

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("x_fwd = %x, y_fwd = %x\n", x_fwd, y_fwd);
    $write("x_bwd = %x, y_bwd = %x\n", x_bwd, y_bwd);
`endif
    if (y_fwd != 16'h1234) $stop;
    if (x_bwd != 16'habcd) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module sub (
    inout wire [15:0] a,
    inout wire [15:0] b
);
  alias a = b;
endmodule
