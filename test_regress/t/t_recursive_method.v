// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Fib;
   function int get_fib(int n);
      if (n == 0 || n == 1)
        return n;
      else
        return get_fib(n - 1) + get_fib(n - 2);
   endfunction
endclass

class FibStatic;
   static function int get_fib(int n);
      if (n == 0 || n == 1)
        return n;
      else
        return get_fib(n - 1) + get_fib(n - 2);
   endfunction
endclass

module t (/*AUTOARG*/);

   initial begin
      Fib fib = new;
      if (fib.get_fib(0) != 0) $stop;
      if (fib.get_fib(1) != 1) $stop;
      if (fib.get_fib(8) != 21) $stop;

      if (FibStatic::get_fib(0) != 0) $stop;
      if (FibStatic::get_fib(1) != 1) $stop;
      if (FibStatic::get_fib(8) != 21) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
