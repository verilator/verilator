// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Alias type check error test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  reg [15:0] out;
  wire [15:0] a;

  alias a = sub_i.btw;

  sub sub_i (
      .clk(clk),
      .out(out)
  );

endmodule

module sub (
    input clk,
    output wire [15:0] out
);

  reg [31:0] counter = 32'h0;
  wire [15:0] btw;

  assign btw = {counter[15:0]};
  assign out = btw;

  always @(posedge clk) begin
    counter += 1;
  end
endmodule
