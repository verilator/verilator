// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jie Xu.

//bug692

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input  wire       clk;

   wire [31:0] 	     result;
   test_if  #(.id(3)) s();
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
  #(parameter id = 0)
   ();

   typedef struct     packed {
      logic 	      a;
      logic [31:0]    b;
   } aType;

   aType a;

   typedef struct     packed {
      logic 	      c;
      logic [31:0]    d;
   } bType;

   bType b;

   modport master (input a, output b);

endinterface
