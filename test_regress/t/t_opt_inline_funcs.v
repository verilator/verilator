// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(
  input  logic [16:0] clearBit_i,
  input  int          clearBit_idx,
  output logic [16:0] clearBit_o
);

   function void allfin;
      $write("*-* All Finished *-*\n");
   endfunction

   task done;
      $finish;
   endtask

   initial begin
      allfin();
      done();
   end

   function automatic logic [16:0] clearBit(logic [16:0] i, int idx);
     i[idx] = 1'b0;
     return i;
   endfunction
   assign clearBit_o = clearBit(clearBit_i, clearBit_idx);

endmodule
