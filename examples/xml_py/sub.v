// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.
// ======================================================================

module sub
  #(parameter type TYPE_t = logic)
   (
    input TYPE_t in,
    output TYPE_t out
    );

   // Some simple logic
   always_comb out = ~ in;

endmodule
