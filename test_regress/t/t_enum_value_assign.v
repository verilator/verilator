// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   localparam logic [9:0] V2 = (1 << 2);
   localparam logic [9:0] V1 = (1 << 1);
   localparam logic [9:0] V0 = (1 << 0);
   typedef enum logic [9:0] {
                             ZERO = '0,
                             VAL0 = V0,
                             VAL1 = V1,
                             VAL01 = V0 | V1
                             } enum_t;

   localparam enum_t PARAMVAL1 = VAL1;
   localparam enum_t PARAMVAL1CONST = enum_t'(2);

   typedef enum {I_ZERO, I_ONE, I_TWO} inte_t;
   localparam inte_t I_PARAM = inte_t'(1);

   initial begin
      enum_t e;
      e = VAL01;
      if (e != VAL01) $stop;

      if (PARAMVAL1 != VAL1) $stop;
      if (PARAMVAL1CONST != VAL1) $stop;

      if (I_PARAM != I_ONE) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
