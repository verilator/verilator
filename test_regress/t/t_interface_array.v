// DESCRIPTION: Verilator: Functionally demonstrate an array of interfaces
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

interface foo_intf;
   logic a;

   modport source (
      output a
   );

   modport sink (
      input a
   );
endinterface

function integer identity (input integer val);
   return val;
endfunction

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   localparam N = 5;

   logic [N-1:0] a_in;
   logic [N-1:0] a_out;
   logic [N-1:0] ack_out;

   foo_intf foos [N-1:0] ();

   // Deferred link dotting with genvars
   generate
      genvar 	 i;
      for (i = 0; i < N-4; i++) begin : someLoop
	 assign ack_out[i] = a_in[i];
	 assign foos[i].a = a_in[i];
	 assign a_out[i] = foos[i].a;
      end
   endgenerate

   // Defferred link dotting with localparam
   localparam THE_LP = N-3;
   assign ack_out[THE_LP] = a_in[THE_LP];
   assign foos[THE_LP].a = a_in[THE_LP];
   assign a_out[THE_LP] = foos[THE_LP].a;

   // Defferred link dotting with arithmetic expression
   assign ack_out[N-2] = a_in[N-2];
   assign foos[N-2].a = a_in[N-2];
   assign a_out[N-2] = foos[N-2].a;

   // Defferred link dotting with funcrefs
   assign ack_out[identity(N-1)] = a_in[identity(N-1)];
   assign foos[identity(N-1)].a = a_in[identity(N-1)];
   assign a_out[identity(N-1)] = foos[identity(N-1)].a;

   initial a_in = '0;
   always @(posedge clk) begin
      a_in <= a_in + { {N-1 {1'b0}}, 1'b1 };

      if (ack_out != a_out) begin
	 $display("%%Error: Interface and non-interface paths do not match: 0b%b 0b%b",
		  ack_out, a_out);
	 $stop;
      end

      if (& a_in) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
