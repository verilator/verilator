// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

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
