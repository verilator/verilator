// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Class1 #(type T);
  static function int get_p();
    return 7;
  endfunction
endclass

class Class2 #(type T) extends Class1 #(T);
   static function int get_p2;
     return T::get_p();
   endfunction
endclass

module t;
  initial begin
    typedef Class2#(Class1#(int)) Class;
    if (Class::get_p2() != Class1#(int)::get_p()) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
