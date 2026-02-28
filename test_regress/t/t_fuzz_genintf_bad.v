// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

//bug1588
interface intf;
   logic a;
   modport source(output a);
endinterface

module m1
  (
   input logic value,
   intf.source b
   );
endmodule

module t;
   intf ifs();

   m1 m0(
         j.e(0),
         .b(ifs)
         );

   genvar j;
endmodule
