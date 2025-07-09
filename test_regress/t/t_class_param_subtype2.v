// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Class1 #(type T);
   static function int get();
      return T::Helper::getter();
   endfunction
endclass

class Class2;
   typedef Class2 Helper;
   static function int getter();
      return 13;
   endfunction
endclass

module t;
   initial begin
      if (Class1#(Class2)::get() != 13) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
