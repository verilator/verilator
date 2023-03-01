// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface class Icls;
   typedef int int_t;
   pure virtual function int ifunc(int_t val);
endclass

interface class IclsExt extends Icls;
   // Typedefs seen by extended, but not implements (need ::)
   pure virtual function int ifuncExt(int_t v1, int_t v2);
endclass

class IclsImp implements Icls;
   function int ifunc(Icls::int_t val);
      return val + 1;
   endfunction
endclass

// Bad, already have error for
// class IclsImp2 implements Icls;
//    function int ifunc(int_t val);  // Bad int_t not typedefed
//    endfunction
// endclass

module t(/*AUTOARG*/);

   IclsImp i1;

   initial begin
      i1 = new;
      if (i1.ifunc(2) != 3) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
