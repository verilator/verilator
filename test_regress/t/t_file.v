// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

`include "verilated.v"

module t;
   `verilator_file_descriptor file;

   initial begin
      // Display formatting
`ifdef verilator
      if (file != 0) $stop;
      $fwrite(file, "Never printed, file closed\n");
`endif

      file = $fopen("obj_dir/t_file_test.log","w");	// The "w" is required so we get a FD not a MFD

      $fdisplay(file, "[%0t] hello v=%x", $time, 32'h12345667);
      $fwrite(file, "[%0t] %s\n", $time, "Hello2");

      $fclose(file);
`ifdef verilator
      if (file != 0) $stop;
      $fwrite(file, "Never printed, file closed\n");
`endif

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
