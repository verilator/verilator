// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef enum logic [1:0] {A, B, C } letters_t;

module SubA
  #(parameter letters_t LETTER = A)
   ();
endmodule

module SubB
  #(parameter letters_t LETTER = letters_t'(0))
   ();
endmodule

module t ();
   SubA suba0 ();
   SubA #(.LETTER(letters_t'(1))) suba1 ();
   SubB #(.LETTER(letters_t'(1))) subb2 ();
endmodule
