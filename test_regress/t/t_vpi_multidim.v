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

   logic [3:2][5:3] arr_cdata [1:0][2:1]; // 2x3 (6) bit words
   logic [7:6][12:7] arr_sdata [5:4][6:5]; // 2x6 (12) bit words
   logic [11:10][25:11] arr_idata [9:8][10:9]; // 2x15 (30) bit words
   logic [15:14][44:15] arr_qdata [13:12][14:13]; // 2x30 (60) bit words
   logic [19:18][81:19] arr_wdata [17:16][18:17]; // 2x63 (126) bit words

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
