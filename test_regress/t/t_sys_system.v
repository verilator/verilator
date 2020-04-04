// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   integer i;

   initial begin
`ifndef VERILATOR
 `ifndef VCS
  `ifndef NC
      $system();  // Legal per spec, but not supported everywhere and nonsensical
  `endif
 `endif
`endif
      $system("exit 0");
      $system("echo hello");
`ifndef VCS
      i = $system("exit 0");
      if (i!==0) $stop;
      i = $system("exit 10");
      if (i!==10) $stop;
      i = $system("exit     20"); // Wide
      if (i!==20) $stop;
`endif

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
