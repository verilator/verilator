// DESCRIPTION: Verilator: Verilog Test module for issue #221
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Julien Margetts (Originally provided by Adrien Le Masle)
// SPDX-License-Identifier: Unlicense

module verilator_latch
(
   input  logic        state,
   output logic [31:0] b
);

   function logic [31:0 ] toto ();
      logic [31:0] res;
      res = 10;
      return res;
   endfunction

   always_comb
   begin
      b = 0;
      if (state)
          b = toto();
   end

endmodule;
