// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2014 Jie Xu
// SPDX-License-Identifier: CC0-1.0

//bug692

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input  wire       clk;

   wire [31:0]       result;
   test_if  #(.ID(3)) s();
   sub_test U_SUB_TEST(s.a.b, result);  // the line causing error
endmodule : t

// ---------------------------------------------------------------------------

module sub_test
  (
   input [31:0]  b,
   output [31:0] c
   );
   assign c = b;
endmodule

// ---------------------------------------------------------------------------

interface test_if
  #(parameter ID = 0)
   ();

   typedef struct     packed {
      logic           a;
      logic [31:0]    b;
   } aType;

   aType a;

   typedef struct     packed {
      logic           c;
      logic [31:0]    d;
   } bType;

   bType b;

   modport master (input a, output b);

endinterface
