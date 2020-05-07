// DESCRIPTION: Verilator: Verilog Test module
//
// The code as shown makes a really big file name with Verilator.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

`define LONG_NAME_MOD modlongnameiuqyrewewriqyewroiquyweriuqyewriuyewrioryqoiewyriuewyrqrqioeyriuqyewriuqyeworqiurewyqoiuewyrqiuewoyewriuoeyqiuewryqiuewyroiqyewiuryqeiuwryuqiyreoiqyewiuryqewiruyqiuewyroiuqyewroiuyqewoiryqiewuyrqiuewyroqiyewriuqyewrewqroiuyqiuewyriuqyewroiqyewroiquewyriuqyewroiqewyriuqewyroiqyewroiyewoiuryqoiewyriuqyewiuryqoierwyqoiuewyrewoiuyqroiewuryewurqyoiweyrqiuewyreqwroiyweroiuyqweoiuryqiuewyroiuqyroie
`define LONG_NAME_SUB sublongnameiuqyrewewriqyewroiquyweriuqyewriuyewrioryqoiewyriuewyrqrqioeyriuqyewriuqyeworqiurewyqoiuewyrqiuewoyewriuoeyqiuewryqiuewyroiqyewiuryqeiuwryuqiyreoiqyewiuryqewiruyqiuewyroiuqyewroiuyqewoiryqiewuyrqiuewyroqiyewriuqyewrewqroiuyqiuewyriuqyewroiqyewroiquewyriuqyewroiqewyriuqewyroiqyewroiyewoiuryqoiewyriuqyewiuryqoierwyqoiuewyrewoiuyqroiewuryewurqyoiweyrqiuewyreqwroiyweroiuyqweoiuryqiuewyroiuqyroie
`define LONG_NAME_VAR varlongnameiuqyrewewriqyewroiquyweriuqyewriuyewrioryqoiewyriuewyrqrqioeyriuqyewriuqyeworqiurewyqoiuewyrqiuewoyewriuoeyqiuewryqiuewyroiqyewiuryqeiuwryuqiyreoiqyewiuryqewiruyqiuewyroiuqyewroiuyqewoiryqiewuyrqiuewyroqiyewriuqyewrewqroiuyqiuewyriuqyewroiqyewroiquewyriuqyewroiqewyriuqewyroiqyewroiyewoiuryqoiewyriuqyewiuryqoierwyqoiuewyrewoiuyqroiewuryewurqyoiweyrqiuewyreqwroiyweroiuyqweoiuryqiuewyroiuqyroie

module t ();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   logic `LONG_NAME_VAR;

   `LONG_NAME_MOD
     `LONG_NAME_SUB
       ();

endmodule

module `LONG_NAME_MOD ();
   // Force Verilator to make a new class
   logic a1 /* verilator public */;
endmodule
