// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

virtual class VBase;
endclass

class Cls#(parameter type T = VBase);
   T t;
   function new;
      t = new;
   endfunction
endclass

virtual class ClsVirt#(parameter type T);
endclass

module t;
   initial begin
      Cls c = new;  // Error
      ClsVirt#(VBase) cv = new;  // Error
      $stop;
   end
endmodule
