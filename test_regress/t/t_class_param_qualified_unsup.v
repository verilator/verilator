// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Self #(type T = int);
  class Inner #(type U = int);
  endclass

  Self::Inner #(T) qualified = new;
  Self#(T)::Inner #(bit [14:0]) qualified_wide = new;
endclass

module t;
  Self #(int) owner_int = new;
  Self #(bit [6:0]) owner_bit7 = new;
endmodule
