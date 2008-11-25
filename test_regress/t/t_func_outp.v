// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (clk);

   input clk;

   reg [7:0] 	a,b;
   wire [7:0] 	z;

   mytop u0 ( a, b, clk, z );

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 //$write("%d %x\n", cyc, z);
	 if (cyc==1) begin
	    a <= 8'h07;
	    b <= 8'h20;
	 end
	 if (cyc==2) begin
	    a <= 8'h8a;
	    b <= 8'h12;
	 end
	 if (cyc==3) begin
	    if (z !== 8'hdf) $stop;
	    a <= 8'h71;
	    b <= 8'hb2;
	 end
	 if (cyc==4) begin
	    if (z !== 8'hed) $stop;
	 end
	 if (cyc==5) begin
	    if (z !== 8'h4d) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule // mytop

module inv(
             input [ 7:0 ]  a,
             output  [ 7:0 ]  z
             );
   wire [7:0] 		      z = ~a;
endmodule


module ftest(
             input [ 7:0 ]  a,
                            b,   // Test legal syntax
             input clk,
             output  [ 7:0 ]  z
             );

   wire [7:0] 		      zi;
   reg [7:0] 		      z;

   inv u1 (.a(myadd(a,b)),
	   .z(zi));


   always @ ( posedge clk ) begin
      z <= myadd( a, zi );
   end

   function [ 7:0 ] myadd;
      input [7:0] ina;
      input [7:0] inb;

      begin
         myadd = ina + inb;
      end
   endfunction // myadd

endmodule // ftest

module mytop (
           input [ 7:0 ]  a,
                          b,
           input clk,
           output  [ 7:0 ]  z
           );

   ftest u0( a, b, clk, z );

endmodule // mytop
