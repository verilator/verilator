// DESCRIPTION: Verilator: Verilog Test module
// SPDX-License-Identifier: CC0-1.0

class Other;
   static int shared = 11;
endclass

class Plain;
   int x = 1;
   static int shared = 3;
   static int count = 0;
   function new(); count++; endfunction
   function int argument(int x); return x; endfunction
   function int local_value(); int x = 7; return x; endfunction
   static function int foreign_value(); return Other::shared; endfunction
endclass

class Outer #(int ID = 1);
   class Inner;
      static int count = 0;
      function new(); count++; endfunction
      function int owner(); return ID; endfunction
   endclass
   class Unused #(type T = int);
      T value;
      function new(); value = new; endfunction
   endclass
endclass

module t;
   typedef Outer#() O0;
   typedef Outer#(1) O1;
   typedef Outer#(2) O2;
   typedef O0::Inner I0;
   typedef O1::Inner I1;
   typedef O2::Inner I2;

   initial begin
      automatic Plain p = new;
      automatic I0 i0 = new;
      automatic I1 i1 = new;
      automatic I2 i2 = new;
      i0 = i1;
      if (Plain::count != 1) $stop;
      if (p.argument(9) != 9 || p.local_value() != 7) $stop;
      if (Plain::foreign_value() != 11 || Other::shared != 11) $stop;
      if (I0::count != 2 || I1::count != 2 || I2::count != 1) $stop;
      if (i0.owner() != 1 || i2.owner() != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
