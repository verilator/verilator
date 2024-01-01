// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import "DPI-C" context function int mon_check();

parameter int dollarUnitInt /*verilator public_flat_rd*/ = 3;

package somepackage;
   parameter int someInt /*verilator public_flat_rd*/ = 5;
   parameter int anotherInt /*verilator public_flat_rd*/ = 6;
endpackage

module t (/*AUTOARG*/
   ); /*verilator public_module*/

   parameter int someOtherInt /* verilator public_flat_rd*/ = 7;
   parameter int yetAnotherInt /* verilator public_flat_rd*/ = 9;
   parameter int stillAnotherInt /* verilator public_flat_rd*/ = 17;

   integer status;

   initial begin
      status = mon_check();
      if (status!=0) begin
         $write("%%Error: t_vpi_package.cpp:%0d: C Test failed\n", status);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule : t
