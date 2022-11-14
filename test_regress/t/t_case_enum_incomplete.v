// DESCRIPTION: Verilator: SystemVerilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic in 
  );

  enum logic [1:0] {S0,S1,S2} state, next;

  always_comb begin: set_next_state
    next = state; //default value
    unique case ( state )
      S0: if (in==1'b1) 
           next = S1;
          else
           next = S0;
      S1: if (in==1'b0) 
            next = S2;
          else if (in==1'b1)
            next = S1;
      S2: if (in==1'b1) 
            next = S1;
          else if (in==1'b0)
            next = S2;
    endcase
  
  end: set_next_state

endmodule
