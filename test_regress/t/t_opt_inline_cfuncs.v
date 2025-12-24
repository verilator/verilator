// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test module designed to generate multiple small CFuncs that can be inlined
// Uses generate to create multiple sub-module instances
module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  integer cyc = 0;

  parameter CNT = 8;

  wire [31:0] w[CNT:0];
  reg [31:0] w0;
  assign w[0] = w0;

  // Generate multiple sub-modules - each creates CFuncs that can be inlined
  generate
    for (genvar g = 0; g < CNT; g++) begin : gen_sub
      sub sub_inst (
          .clk(clk),
          .i(w[g]),
          .z(w[g+1])
      );
    end
  endgenerate

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      w0 <= 32'h10;
    end
    else if (cyc == 10) begin
      // Each sub adds 1, so final value is 0x10 + 8 = 0x18
      if (w[CNT] !== 32'h18) begin
        $write("%%Error: w[CNT]=%0x, expected 0x18\n", w[CNT]);
        $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

// Small sub-module that generates inlineable CFuncs
module sub (
    input clk,
    input [31:0] i,
    output reg [31:0] z
);
  reg [7:0] local_a;
  reg [7:0] local_b;

  always @(posedge clk) begin
    local_a <= i[7:0];
    local_b <= 8'd1;
    z <= i + {24'b0, local_b};
  end
endmodule
