// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [65:0] idx /*verilator public*/; initial idx = 1;


   wire unlikely = idx > 200; 
   
   typedef enum logic {UP, DOWN} dir_t;
   dir_t direction;
   always_comb direction = idx % 2 == 0 ? UP : DOWN;


   // always_ff @(negedge clk) if (selected == MGMT) $error("no");
   always @(posedge clk) begin
      if (idx > 100) begin
           $write("*-* All Finished *-*\n");
           $finish;
      end


      case(direction)
         DOWN: idx = idx+3;
         UP: idx = idx-1;
         default: begin 
            // this if just gets rid of branch pred on default^
            if(unlikely== '1) begin
               $write("never\n");
            end
         end
      endcase

      
   end

endmodule
