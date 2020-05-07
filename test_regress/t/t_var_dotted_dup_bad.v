// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   generate
      begin
         eh2_ram dccm_bank (.*);
      end
      begin
         eh2_ram dccm_bank (.*);  // Error: duplicate
      end
   endgenerate

endmodule

module eh2_ram ();
endmodule
