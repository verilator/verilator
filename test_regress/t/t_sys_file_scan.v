// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

`include "verilated.v"

module t;
   `verilator_file_descriptor infile, outfile;
   integer count, a;

   initial begin
      infile = $fopen("t/t_sys_file_scan_input.dat", "r");
      outfile = $fopen("obj_dir/t_sys_file_scan_test.log", "w");

      count = 1234;
      $display("count == %d, infile %d, outfile %d", count, infile, outfile);
      count = $fscanf(infile, "%d\n", a);
      $display("count == %d, infile %d, outfile %d", count, infile, outfile);
      $fwrite(outfile, "# a\n");
      $fwrite(outfile, "%d\n", a);
      $fclose(infile);
      $fclose(outfile);

      $write("*-* All Finished *-*\n");
      $finish(0);  // Test arguments to finish
   end

endmodule
