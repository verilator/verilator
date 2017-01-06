// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Andrew Bardsley.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // This won't compile with tracing as an incorrect declaration is made for
   // the temp variables used to represent the elements of localparam v
   typedef struct packed {
      logic [2:0][31:0] a;
   } t;

   localparam t v[2:0] = '{
       '{'{32'h10000002, 32'h10000001, 32'h10000000}},
       '{'{32'h20000002, 32'h20000001, 32'h20000000}},
       '{'{32'h30000002, 32'h30000001, 32'h30000000}}
   };

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
