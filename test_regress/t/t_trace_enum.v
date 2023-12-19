// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef enum logic [1:0] {VAL_A, VAL_B, VAL_C, VAL_D} state_t;

interface MyIntf;
   state_t state;
endinterface


module t (clk);
   input clk;

   MyIntf #() sink ();
   state_t v_enumed;

   typedef enum logic [1:0] {VAL_X, VAL_Y, VAL_Z} other_state_t;
   other_state_t v_other_enumed;

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
