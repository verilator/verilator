// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t();

class A;
   int num;
   function new(int num);
      this.num = num;
   endfunction
endclass

class B;
   static A obj = new(2);
endclass

class C;
   static A obj = new(5);
endclass

   initial begin
      #1;
      $display("Bobj=%p Cobj=%p eq=%p", B::obj, C::obj, (B::obj == C::obj));
      if (B::obj == C::obj) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
