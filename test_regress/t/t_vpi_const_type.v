// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import "DPI-C" context function int mon_check();

module t (/*AUTOARG*/
   ); /*verilator public_module*/

   parameter int intParam /*verilator public_flat_rd*/ = 5;
   parameter real realParam /*verilator public_flat_rd*/ = 2.3;
   parameter time timeParam /*verilator public_flat_rd*/ = 0;
   parameter string strParam /*verilator public_flat_rd*/ = "abc";

   logic [31:0] signal /*verilator public_flat_rw*/;

   int status;

   initial begin
      status = mon_check();
      if (status!=0) begin
         $write("%%Error: t_vpi_const_type.cpp:%0d: C Test failed\n", status);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule : t
