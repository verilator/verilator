// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module class_tb ();
interface class Ibase;
   pure virtual function int fn();
endclass

interface class Ic1 extends Ibase;
   pure virtual function int fn1();
endclass

interface class Ic2 extends Ibase;
   pure virtual function int fn2();
endclass

interface class Ic3 extends Ic1, Ic2;
endclass

class Cls implements Ic3;
   virtual function int fn();
      return 10;
   endfunction
   virtual function int fn1();
      return 1;
   endfunction
   virtual function int fn2();
      return 2;
   endfunction
endclass

   initial begin
      Cls cls;
      Ibase ibase;
      Ic1 ic1;
      Ic2 ic2;
      Ic3 ic3;
      cls = new;
      if (cls.fn() != 10) $stop;
      if (cls.fn1() != 1) $stop;
      if (cls.fn2() != 2) $stop;
      ibase = cls;
      ic1 = cls;
      ic2 = cls;
      ic3 = cls;
      if (ibase.fn() != 10) $stop;
      if (ic1.fn() != 10) $stop;
      if (ic2.fn() != 10) $stop;
      if (ic3.fn() != 10) $stop;
      if (ic1.fn1() != 1) $stop;
      if (ic2.fn2() != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
