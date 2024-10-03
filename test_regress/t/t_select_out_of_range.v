// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module serial_adder(
  input  cin,
  output cout
);
    localparam WIDTH = 8;

    wire [WIDTH:0] c;

    generate for (genvar i = 0; i < WIDTH; i++)
        full_adder fa(c[i+1]);
    endgenerate

    assign c[0] = cin;
    assign cout = c[WIDTH+1]; // intentional out-of-range

endmodule

module full_adder (output cout);
endmodule
