// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ns
module t;
   p p ();

   // Also check not-found modules
   localparam NOT = 0;
   if (NOT) begin
      NotFound not_found(.*);
   end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

`timescale 1ns/1ns
program p;
endprogram

`celldefine
`timescale 1ns/1ns

primitive a_udp(out, in);
output out;
input in;
reg out;

table
0       :   1;
1       :   0;
?       :   ?;
x       :   x;
endtable
endprimitive
`endcelldefine

`celldefine
module c_not(in, out);
input in;
output out;
assign out = !in1;
endmodule
`endcelldefine
