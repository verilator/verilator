// DESCRIPTION: Verilator: Verilog Test module
//
// Modport import export list test
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Goekce Aydos.
// SPDX-License-Identifier: CC0-1.0

interface intf;
   logic l;
   function void f1();
   endfunction
   function void f2();
   endfunction
   function void f3();
   endfunction
   function void f4();
   endfunction

   modport mpi
     (
      import f1, f2,
      input l,
      import f3, f4
      );
   modport mpo
     (
      output l,
      import f1, f2, f3, f4
      );
endinterface

module mo (intf.mpo intf0);
   function void ef1();
      intf0.f1();
      intf0.f2();
   endfunction
   function void ef2();
      intf0.f3();
      intf0.f4();
   endfunction

   initial begin
      ef1();
      ef2();
   end
endmodule

module mi (intf.mpi intf0);
endmodule

module t;
   intf intf0();
   mi mi(.*);
   mo mo(.*);
endmodule
