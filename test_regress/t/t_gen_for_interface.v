// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Johan Bjork.
// SPDX-License-Identifier: CC0-1.0

parameter N = 5;

interface intf;
   logic [N-1:0] data;
endinterface

module t (
   input logic clk
   );
   intf localinterface [N-1:0]();

   generate
      genvar   i,j;
      for(i = 0; i  < N; i++) begin
         logic [N-1:0] dummy;
         for(j = 0; j < N; j++) begin
            assign dummy[j] = localinterface[j].data[i];
         end
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
