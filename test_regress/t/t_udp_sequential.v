// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Mike Thyer.
// SPDX-License-Identifier: CC0-1.0

primitive d_edge_ff (q, clock, data);
 output q; reg q;
 input clock, data;
 initial q = 1'b1;
 table
     // clock data q q+
      // obtain output on rising edge of clock
     (01) 0 : ? : 0 ;
     (01) 1 : ? : 1 ;
     (1?) 0 : ? : 1 ;
     (1?) 1 : ? : 0 ;
 endtable
endprimitive

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   reg d, q;
   d_edge_ff g (q, clk, d);

   int cycle=0;
   initial d = 0;
   always @(posedge clk or negedge clk) begin
     cycle <= cycle+1;
     if (cycle==0) begin
        d <= 1;
     end
     else if (cycle==1) begin
        d <= 0;
        if (q != 0) $stop;
     end
     else if (cycle==2) begin
        if (q != 0) $stop;
     end
     else if (cycle==3) begin
        if (q != 0) $stop;
     end
     else if (cycle==4) begin
        d <= 1;
        if (q != 1) $stop;
     end
     else if (cycle==5) begin
        if (q != 0) $stop;
     end
     else if (cycle==6) begin
        if (q != 0) $stop;
     end
     else if (cycle==7) begin
        if (q != 1) $stop;
     end
     else if (cycle >= 8) begin
        if (q != 0) $stop;;
        $write("*-* All Finished *-*\n");
        $finish;
     end
   end
endmodule
