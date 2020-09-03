// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Jonathon Donaldson.
// SPDX-License-Identifier: CC0-1.0

module t_bitsel_enum
  (
   output out0,
   output out1
   );

   localparam [6:0] CNST_VAL = 7'h22;

   enum   logic [6:0] {
                       ENUM_VAL = 7'h33
                       } MyEnum;

   assign out0 = CNST_VAL[0];
   // Not supported by NC-verilog nor VCS, but other simulators do
   assign out1 = ENUM_VAL[0]; // named values of an enumeration should act like constants so this should work just like the line above works

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
