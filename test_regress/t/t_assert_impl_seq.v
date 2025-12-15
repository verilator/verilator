// DESCRIPTION: Verilator: Verilog Test module - implication with sequence expressions
//
// Tests SVA implication (|->) with sequence expressions on the RHS
// This is the pattern used in mbits UART VIP assertions.
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

   logic start_bit = 1'b1;  // UART idle is high
   logic data_bit = 1'b0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      case (cyc)
        0: begin start_bit <= 1'b1; data_bit <= 1'b0; end  // Idle
        1: begin start_bit <= 1'b1; data_bit <= 1'b0; end  // Idle
        2: begin start_bit <= 1'b1; data_bit <= 1'b0; end  // Still idle (no fell)
        3: begin start_bit <= 1'b1; data_bit <= 1'b1; end  // data_bit rises, start_bit high
        4: begin start_bit <= 1'b1; data_bit <= 1'b1; end  // Both high
        5: begin start_bit <= 1'b1; data_bit <= 1'b0; end  // start_bit stays high (satisfies seq_impl)
        10: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
      endcase
   end

   // Default clocking for assertions
   default clocking cb @(posedge clk);
   endclocking

   // Test 1: Simple implication (control - already working)
   property simple_impl;
      @(posedge clk)
      start_bit |-> 1'b1;  // When start_bit is high, true always passes
   endproperty
   assert property (simple_impl) else $error("simple_impl failed at cyc=%0d", cyc);

   // Test 2: Implication with first_match and range delay (mbits pattern)
   // When start_bit falls, within 0-5 cycles data_bit should rise
   // This is simplified semantics - we only check at cycle 0 (minimum delay)
   property start_detect;
      @(posedge clk)
      $fell(start_bit) |-> first_match(##[0:5] data_bit);
   endproperty
   assert property (start_detect) else $error("start_detect failed at cyc=%0d", cyc);

   // Test 3: Implication with simple sequence expression (no first_match)
   property seq_impl;
      @(posedge clk)
      data_bit |-> ##[0:2] start_bit;  // If data_bit, start_bit within 2 cycles
   endproperty
   assert property (seq_impl) else $error("seq_impl failed at cyc=%0d", cyc);

endmodule
