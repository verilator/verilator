// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off LATCH

module t_case_huge_sub4 (/*AUTOARG*/
   // Outputs
   outq,
   // Inputs
   index
   );

   input [7:0] index;
   output [9:0] outq;

   // =============================
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [9:0]            outq;
   // End of automatics

   // =============================
   always @(/*AS*/index) begin
      case (index)
        // default below: no change
        8'h00: begin outq = 10'h001; end
        8'he0: begin outq = 10'h05b; end
        8'he1: begin outq = 10'h126; end
        8'he2: begin outq = 10'h369; end
        8'he3: begin outq = 10'h291; end
        8'he4: begin outq = 10'h2ca; end
        8'he5: begin outq = 10'h25b; end
        8'he6: begin outq = 10'h106; end
        8'he7: begin outq = 10'h172; end
        8'he8: begin outq = 10'h2f7; end
        8'he9: begin outq = 10'h2d3; end
        8'hea: begin outq = 10'h182; end
        8'heb: begin outq = 10'h327; end
        8'hec: begin outq = 10'h1d0; end
        8'hed: begin outq = 10'h204; end
        8'hee: begin outq = 10'h11f; end
        8'hef: begin outq = 10'h365; end
        8'hf0: begin outq = 10'h2c2; end
        8'hf1: begin outq = 10'h2b5; end
        8'hf2: begin outq = 10'h1f8; end
        8'hf3: begin outq = 10'h2a7; end
        8'hf4: begin outq = 10'h1be; end
        8'hf5: begin outq = 10'h25e; end
        8'hf6: begin outq = 10'h032; end
        8'hf7: begin outq = 10'h2ef; end
        8'hf8: begin outq = 10'h02f; end
        8'hf9: begin outq = 10'h201; end
        8'hfa: begin outq = 10'h054; end
        8'hfb: begin outq = 10'h013; end
        8'hfc: begin outq = 10'h249; end
        8'hfd: begin outq = 10'h09a; end
        8'hfe: begin outq = 10'h012; end
        8'hff: begin outq = 10'h114; end
        default: ; // No change
      endcase
   end
endmodule
