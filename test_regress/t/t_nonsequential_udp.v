// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Mike Thyer.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   reg a, b, sel, z;
   udp_mux2(z, a, b, sel);

   int cycle=0;

   always @(posedge clk) begin
     cycle <= cycle+1;
     if (cycle==0) begin
        a = 0;
        b = 1;
        sel = 0;
     end
     else if (cycle==1) begin
        a = 1;
        b = 1;
        sel = 0;
        if (z != 0) $stop;
     end
     else if (cycle==2) begin
        a = 0;
        b = 1;
        sel = 0;
        if (z != 1) $stop;
     end
     else if (cycle==3) begin
        a = 1;
        b = 0;
        sel = 0;
        if (z != 0) $stop;
     end
     else if (cycle==4) begin
        if (z != 1) $stop;
     end
     else if (cycle >= 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
     end
   end
endmodule

primitive udp_mux2 (z, a, b, sel);
   output z;
   input  a, b, sel;
   table
      //a b  s   o
      ?   1  1 : 1 ;
      ?   0  1 : 0 ;
      1   ?  0 : 1 ;
      0   ?  0 : 0 ;
      1   1  x : 1 ;
      // Next blank line is intentional for parser

      // Next \ at EOL is intentional for parser
      0   0  x \
               : 0 ;
   endtable
endprimitive


