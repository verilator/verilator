// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface class Icempty;
endclass : Icempty

interface class Icls1;
   localparam LP1 = 1;
   pure virtual function int icf1;
   pure virtual function int icfboth;
   pure virtual function int icfpartial;
endclass

interface class Iext1 extends Icls1;
   pure virtual function int icf101;
endclass

interface class Icls2;
   pure virtual function int icf2(int in);
   pure virtual function int icfboth;
endclass

virtual class Base implements Iext1, Icls2;
   virtual function int icf1;
      return 1;
   endfunction
   virtual function int icf101;
      return 101;
   endfunction
   virtual function int icf2(int in);
      return in + 2;
   endfunction
   virtual function int icfboth;
      return 3;
   endfunction
   pure virtual function int icfpartial;
endclass

class Cls extends Base;
   virtual function int icfpartial;
      return 62;
   endfunction
endclass

module t(/*AUTOARG*/);

   Cls c;
   Iext1 i1;

   initial begin
      if (Icls1::LP1 != 1) $stop;

      c = new;
      if (c.icf1() != 1) $stop;
      if (c.icf101() != 101) $stop;
      if (c.icf2(1000) != 1002) $stop;
      if (c.icfpartial() != 62) $stop;

      i1 = c;
      if (i1.icf1() != 1) $stop;
      if (i1.icf101() != 101) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
