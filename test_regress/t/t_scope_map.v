// DESCRIPTION: Verilator: Test symbol table scope map and general public
// signal reflection
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module t
  (
   input wire CLK
   );

   foo #(.WIDTH (1)) foo1 (.*);
   foo #(.WIDTH (7)) foo7 (.*);
   foo #(.WIDTH (8)) foo8 (.*);
   foo #(.WIDTH (32)) foo32 (.*);
   foo #(.WIDTH (33)) foo33 (.*);
   foo #(.WIDTH (40)) foo40 (.*);
   foo #(.WIDTH (41)) foo41 (.*);
   foo #(.WIDTH (64)) foo64 (.*);
   foo #(.WIDTH (65)) foo65 (.*);
   foo #(.WIDTH (96)) foo96 (.*);
   foo #(.WIDTH (97)) foo97 (.*);
   foo #(.WIDTH (128)) foo128 (.*);
   foo #(.WIDTH (256)) foo256 (.*);
   foo #(.WIDTH (1024)) foo1024 (.*);
   bar #(.WIDTH (1024)) bar1024 (.*);

endmodule

module foo
  #(
    parameter WIDTH = 32
    )
   (
    input CLK
    );

   logic [ ( ( WIDTH + 7 ) / 8 ) * 8 - 1 : 0 ] initial_value;
   logic [ WIDTH - 1 : 0 ] value_q /* verilator public */;
   integer i;

   initial begin
      initial_value = '1;

      for (i = 0; i < WIDTH / 8; i++)
        initial_value[ i * 8 +: 8 ] = i[ 7 : 0 ];

      value_q = initial_value[ WIDTH - 1 : 0 ];
   end

   always @(posedge CLK)
     value_q <= ~value_q;

endmodule

module bar
  #(
    parameter WIDTH = 32
    )
   (
    input CLK
    );

   foo #(.WIDTH (WIDTH)) foo (.*);

endmodule
