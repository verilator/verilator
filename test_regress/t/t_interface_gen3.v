// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

// Very simple test for interface pathclearing

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   ifc #(2) itopa();
   ifc #(4) itopb();

   sub ca (.isub(itopa.out_modport),
	   .clk);
   sub cb (.isub(itopb.out_modport),
	   .clk);

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d result=%b  %b\n",$time, cyc, itopa.valueo, itopb.valueo);
`endif
      cyc <= cyc + 1;
      itopa.valuei <= cyc[1:0];
      itopb.valuei <= cyc[3:0];
      if (cyc==1) begin
	 if (itopa.WIDTH != 2) $stop;
	 if (itopb.WIDTH != 4) $stop;
	 if ($bits(itopa.valueo) != 2) $stop;
	 if ($bits(itopb.valueo) != 4) $stop;
	 if ($bits(itopa.out_modport.valueo) != 2) $stop;
	 if ($bits(itopb.out_modport.valueo) != 4) $stop;
      end
      if (cyc==4) begin
	 if (itopa.valueo != 2'b11) $stop;
	 if (itopb.valueo != 4'b0011) $stop;
      end
      if (cyc==5) begin
	 if (itopa.valueo != 2'b00) $stop;
	 if (itopb.valueo != 4'b0100) $stop;
      end
      if (cyc==20) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

interface ifc
  #(parameter WIDTH = 1);
   // verilator lint_off MULTIDRIVEN
   logic [WIDTH-1:0] valuei;
   logic [WIDTH-1:0] valueo;
   // verilator lint_on MULTIDRIVEN
   modport out_modport (input valuei, output valueo);
endinterface

// Note not parameterized
module sub
   (
   ifc.out_modport isub,
   input clk
   );
   always @(posedge clk) isub.valueo <= isub.valuei + 1;
endmodule
