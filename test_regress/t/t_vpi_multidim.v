// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/
    // Inputs
   clk
   ); /*verilator public_module*/

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   input clk;

   logic [1:0][2:0] arr_cdata [1:0][1:0]; // 2x3 (6) bit words
   logic [1:0][5:0] arr_sdata [1:0][1:0]; // 2x6 (12) bit words
   logic [1:0][14:0] arr_idata [1:0][1:0]; // 2x15 (30) bit words
   logic [1:0][29:0] arr_qdata [1:0][1:0]; // 2x30 (60) bit words
   logic [1:0][62:0] arr_wdata [1:0][1:0]; // 2x63 (126) bit words

   int status;

   initial begin
`ifdef VERILATOR
      status = $c32("mon_check()");
`else
      status = $mon_check();
`endif
      if (status!=0) begin
         $write("%%Error: t_vpi_multidim.cpp:%0d: C Test failed\n", status);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule : t
