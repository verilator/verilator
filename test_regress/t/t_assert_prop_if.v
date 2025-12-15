// DESCRIPTION: Verilator: Verilog Test module - Property if/else
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int cyc = 0;

   logic [1:0] mode = 2'd0;
   logic a = 1'b1;
   logic b = 1'b0;
   logic c = 1'b0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      // Cycle through different modes, ensuring the right signal is high
      case (cyc)
        0: begin mode <= 2'd0; a <= 1'b1; b <= 1'b0; c <= 1'b0; end
        1: begin mode <= 2'd0; a <= 1'b1; b <= 1'b0; c <= 1'b0; end
        2: begin mode <= 2'd1; a <= 1'b0; b <= 1'b1; c <= 1'b0; end
        3: begin mode <= 2'd1; a <= 1'b0; b <= 1'b1; c <= 1'b0; end
        4: begin mode <= 2'd2; a <= 1'b0; b <= 1'b0; c <= 1'b1; end
        5: begin mode <= 2'd2; a <= 1'b0; b <= 1'b0; c <= 1'b1; end
        6: begin mode <= 2'd3; a <= 1'b0; b <= 1'b0; c <= 1'b1; end  // mode==3 falls to else
        10: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
      endcase
   end

   // Property with if/else - checks that the right signal is high based on mode
   // When mode==0, check 'a'; when mode==1, check 'b'; otherwise check 'c'
   property prop_if_else;
      @(posedge clk) disable iff (cyc < 2)
      if (mode == 2'd0) a
      else if (mode == 2'd1) b
      else c;
   endproperty

   // Simple property if without else - only checks when mode==0
   // When mode!=0, the property vacuously passes (no else means true)
   property prop_if_only;
      @(posedge clk) disable iff (cyc < 2)
      if (mode == 2'd0) a;
   endproperty

   // Use assertions with the properties
   assert property (prop_if_else) else $error("prop_if_else failed at cyc=%0d mode=%0d a=%b b=%b c=%b", cyc, mode, a, b, c);
   assert property (prop_if_only) else $error("prop_if_only failed at cyc=%0d mode=%0d a=%b", cyc, mode, a);

endmodule
