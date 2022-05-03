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

module t (/*AUTOARG*/
   // Inputs
   clk
   );

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   input clk;

   typedef logic [31:0] word_t;
   reg [31:0] mem0 [16:1] /*verilator public_flat_rw @(posedge clk) */;
   reg [16:1] [31:0] memp32 /*verilator public_flat_rw @(posedge clk) */;
   reg [16:1] [30:0] memp31 /*verilator public_flat_rw @(posedge clk) */;
   reg [15:1] [32:0] memp33 /*verilator public_flat_rw @(posedge clk) */;
   word_t [16:1] memw /*verilator public_flat_rw @(posedge clk) */;
   integer        i, status;

`define CHECK_MEM(mem, words) \
      for (i = words; i > 0; i--) \
        if (integer'(mem[i]) !== i) begin \
          $write("%%Error: %s[%d] : GOT = %d  EXP = %d\n", `"mem`", i, mem[i], i); \
          status = -1; \
        end

   // Test loop
   initial begin
`ifdef VERILATOR
      status = $c32("mon_check()");
`else
     status = $mon_check();
`endif
`ifndef USE_VPI_NOT_DPI
     status = mon_check();
`endif
      if (status!=0) begin
         $write("%%Error: t_vpi_memory.cpp: C Test failed (rc=%0d)\n", status);
         $stop;
      end
      `CHECK_MEM(mem0, 16)
      `CHECK_MEM(memp32, 16)
      `CHECK_MEM(memp31, 16)
      `CHECK_MEM(memp33, 15)
      `CHECK_MEM(memw, 16)
      if (status!=0) begin
         $write("%%Error: Verilog memory checks failed\n");
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule : t
