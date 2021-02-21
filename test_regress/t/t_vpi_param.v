// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef USE_VPI_NOT_DPI
//We call it via $c so we can verify DPI isn't required - see bug572
`else
import "DPI-C" context function int mon_check();
`endif


module t #(
   parameter int WIDTH /* verilator public_flat_rd */ = 32
  ) (/*AUTOARG*/
   // Inputs
   clk
   );

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   input clk;

   localparam int DEPTH /* verilator public_flat_rd */ = 16;
   localparam longint PARAM_LONG /* verilator public_flat_rd */ = 64'hFEDCBA9876543210;
   localparam string PARAM_STR /* verilator public_flat_rd */ = "'some string value'";

   reg [WIDTH-1:0] mem0 [DEPTH:1] /*verilator public_flat_rw @(posedge clk) */;
   integer    i, status;

   // Test loop
   initial begin
`ifdef VERILATOR
      status = $c32("mon_check()");
`endif
`ifdef IVERILOG
     status = $mon_check();
`endif
`ifndef USE_VPI_NOT_DPI
     status = mon_check();
`endif

    if (status!=0) begin
      $write("%%Error: t_vpi_param.cpp:%0d: C Test failed\n", status);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
   end

endmodule : t
