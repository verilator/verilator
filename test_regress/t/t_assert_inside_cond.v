// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   hit,
   // Inputs
   clk
   );

   input clk;
   output logic       hit;

   logic [31:0] addr;
   int          cyc;

   initial addr = 32'h380;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
`ifdef T_ASSERT_INSIDE_COND
      addr <= 32'h380;
`elsif T_ASSERT_INSIDE_COND_BAD
      addr <= 32'h389;
`else
 `error "Bad test define"
`endif
      if (cyc == 9) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always_comb begin
      hit = 0;
      unique case (addr[11:0]) inside
        [12'h380 : 12'h388]: begin
           hit = 1;
        end
      endcase
   end

endmodule
