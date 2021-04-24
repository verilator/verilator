// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   localparam string REGS [0:31]
                     = '{"zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                         "s0/fp", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                         "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6",
                         "fs7", "fs8", "fs9", "fs10", "fs11", "ft8", "ft9",
                         "ft10", "ft11"};
   function string disasm32(logic [4:0] op);
      return $sformatf("lui   %s"     , REGS[op]);
   endfunction
endpackage

module t(/*AUTOARG*/
   // Inputs
   op
   );
   import pkg::*;
   input [4:0] op;
   always_comb begin
        $display("OP: 0x%08x: %s", op, disasm32(op));
   end
endmodule
