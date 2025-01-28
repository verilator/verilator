// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import "DPI-C" context function int mon_check();

parameter int dollarUnitInt = 3;

package somepackage;
   parameter int someInt  = 5;
   parameter int anotherInt = 6;
endpackage

module t (/*AUTOARG*/
   );

   parameter int someOtherInt  = 7;
   parameter int yetAnotherInt = 9;
   parameter int stillAnotherInt = 17;
   parameter int register = 0;
   parameter int n_str = 2;
   // Edge case with pvi code generation
   parameter string someString [n_str] = '{default: ""};
   logic reference;

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
