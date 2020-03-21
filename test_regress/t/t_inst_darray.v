// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by John Stevenson.
// SPDX-License-Identifier: CC0-1.0

typedef logic [63:0] uid_t;
typedef logic [31:0] value_t;

interface the_intf #(parameter M = 5);
   logic 	     valid;
   uid_t           uid;
   value_t [M-1:0] values;

   modport i(
	     output valid,
	     output uid,
	     output values
	     );
   modport t(
	     input valid,
	     input uid,
	     input values
	     );
endinterface

module Contemplator #(
		      parameter IMPL = 0,
		      parameter M    = 5,
		      parameter N    = 1 )
   (
    input logic clk,
    the_intf.i out [N-1:0]
    );

   the_intf #(.M(M)) inp[N-1:0] ();

   DeepThought #(
		 .N    ( N   ))
   ultimateAnswerer(
		    .src  ( inp ),
		    .dst  ( out ));
endmodule

module DeepThought #(
		     parameter N = 1 )
   (
    the_intf.t src[N-1:0],
    the_intf.i dst[N-1:0]
    );
endmodule


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   localparam  M = 5;
   localparam  N = 1;

   the_intf #(.M(M)) out0 [N-1:0] ();
   the_intf #(.M(M)) out1 [N-1:0] ();

   Contemplator #(
		  .IMPL ( 0    ),
		  .M    ( M    ),
		  .N    ( N    ))
   contemplatorOfTheZerothKind(
			       .clk  ( clk  ),
			       .out  ( out0 ));

   Contemplator #(
		  .IMPL ( 1    ),
		  .M    ( M    ),
		  .N    ( N    ))
   contemplatorOfTheFirstKind(
			      .clk  ( clk  ),
			      .out  ( out1 ));
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
