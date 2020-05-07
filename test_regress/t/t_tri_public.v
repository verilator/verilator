// DESCRIPTION: Verilator: Unsupported tristate constructur error
//
// This is a compile only regression test of tristate handling for bug514
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Rob Stoddard.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   data, up_down, clk, reset
   );

   //----------Output Ports--------------
   output [7:0] out;
   //------------Input Ports--------------
   //input [7:0] data ;
   input [7:0] 	data;
   input 	up_down, clk, reset;
   //------------Internal Variables--------
   reg [7:0] 	out;
   logic [7:0] 	q_out;

   //-------------Code Starts Here-------
   always @(posedge clk)
     if (reset) begin // active high reset
        out <= 8'b0 ;
     end else if (up_down) begin
        out <= out + 1;
     end else begin
        out <= q_out;
     end

   // verilator lint_off PINMISSING
   sub_mod sub_mod
     (
      .clk(clk),
      .data(data),
      .reset(reset),
      .q(q_out)
      );
   // verilator lint_on PINMISSING

endmodule

module sub_mod (/*AUTOARG*/
   // Outputs
   q, test_out,
   // Inouts
   test_inout,
   // Inputs
   data, clk, reset
   );

   //-----------Input Ports---------------

   input [7:0] data /*verilator public*/;
   input       clk, reset;
   inout       test_inout;  // Get rid of this, the problem goes away.

   //-----------Output Ports---------------
   output [7:0] q;
   output 	test_out;  // Not assigned,  no problem.

   logic [7:0] 	que;

   // Uncomment this line, the error goes away.
   //assign test_inout = que;

   assign q = que;
   always @ ( posedge clk)
     if (~reset) begin
        que <= 8'b0;
     end else begin
        que <= data;
     end
endmodule
