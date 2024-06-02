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

class Factorial;
   static function int factorial(int n);
      return fact(n, 1);
   endfunction
   static function int fact(int n, int acc);
      if (n < 2)
         fact = acc;
      else
         fact = fact(n - 1, acc * n);
   endfunction
endclass

class Getter3 #(int T=5);
   static function int get_3();
      if (T == 3)
        return 3;
      else
        return Getter3#(3)::get_3();
   endfunction
endclass

module t (/*AUTOARG*/);

   initial begin
      Fib fib = new;
      Getter3 getter3 = new;

      if (fib.get_fib(0) != 0) $stop;
      if (fib.get_fib(1) != 1) $stop;
      if (fib.get_fib(8) != 21) $stop;

      if (FibStatic::get_fib(0) != 0) $stop;
      if (FibStatic::get_fib(1) != 1) $stop;
      if (FibStatic::get_fib(8) != 21) $stop;

      if (Factorial::factorial(0) != 1) $stop;
      if (Factorial::factorial(1) != 1) $stop;
      if (Factorial::factorial(6) != 720) $stop;

      if (getter3.get_3() != 3) $stop;
      if (Getter3#(3)::get_3() != 3) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
