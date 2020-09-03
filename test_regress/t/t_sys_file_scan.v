// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "verilated.v"

`define STRINGIFY(x) `"x`"

module t;
   integer infile, outfile;
   integer count, a;

   initial begin
      infile = $fopen("t/t_sys_file_scan_input.dat", "r");
      outfile = $fopen({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_file_scan_test.log"}, "w");

      count = 1234;
`ifdef TEST_VERBOSE
      $display("-count == %0d, infile %d, outfile %d", count, infile, outfile);
`endif
      count = $fscanf(infile, "%d\n", a);
`ifdef TEST_VERBOSE
      // Ifdefing this out gave bug248
      $display("-count == %0d, infile %d, outfile %d", count, infile, outfile);
`endif
      if (count == 0) $stop;
      $fwrite(outfile, "# a\n");
      $fwrite(outfile, "%d\n", a);
      $fclose(infile);
      $fclose(outfile);

      $write("*-* All Finished *-*\n");
      $finish(0);  // Test arguments to finish
   end

endmodule
