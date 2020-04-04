// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (/*AUTOARG*/
   // Outputs
   someOutput,
   // Inputs
   clk, reset_l, InOne, InTwo
   );

   input         clk;
   input         reset_l;
   input         InOne, InTwo;
   output logic  someOutput;

   typedef enum {
                 STATE_ONE,
                 STATE_TWO,
                 STATE_THREE,
                 STATE_FOUR
                 } some_state_t;

   some_state_t some_FSM;

   always_ff @ (posedge clk or negedge reset_l) begin
      if(!reset_l)
        some_FSM <= some_FSM.first;
      else begin
         unique case (some_FSM)
           STATE_ONE, STATE_TWO, STATE_THREE: begin
              if(InOne & InTwo)
                some_FSM <= some_FSM.next;
              else if(InOne)
                some_FSM <= some_FSM;
              else
                some_FSM <= some_FSM.first;
           end
           default: begin
              some_FSM <= STATE_ONE;
           end
         endcase
      end
   end

   always_comb begin
      someOutput = (some_FSM == STATE_FOUR);
   end
endmodule
