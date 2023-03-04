// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls #(int PARAM = 1);
   parameter OTHER = 12;
endclass

class Other extends Cls#();  // Ok
endclass

class OtherMaybe extends Cls;  // Questionable but others do not warn
endclass

module t (/*AUTOARG*/);

   typedef Cls#(2) Cls2_t;  // Ok
   typedef Cls ClsNone_t;  // Ok

   Cls c;  // Ok

   initial begin
      if (Cls#()::OTHER != 12) $stop;  // Ok
      if (Cls2_t::OTHER != 12) $stop;  // ok

      if (Cls::OTHER != 12) $stop;  // Bad #() required
   end

endmodule
