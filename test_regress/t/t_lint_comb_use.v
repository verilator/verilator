// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   hval,
   // Inputs
   sel
   );

   input  logic [2:0] sel;
   output logic [3:0] hval;

   /*AUTOINPUT*/
   /*AUTOOUTPUT*/

   always_comb begin
      unique case (sel)
        3'h0: hval = 4'hd;
        3'h1: hval = 4'hc;
        3'h7: hval = 4'hf;
        default: begin
	   $ignore ("ERROR : %s [%m]", $sformatf ("Illegal sel = %x", sel));
	   hval = 4'bx;
	end
      endcase
   end
endmodule
