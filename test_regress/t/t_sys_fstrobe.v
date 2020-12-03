// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int cyc = 0;
   int fd;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 5) begin
         fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR),"/open.log"}, "w");
      end
      else if (cyc == 10) begin
         $fstrobe(fd, "[%0t] cyc=%0d", $time, cyc);
         $fstrobe(fd, "[%0t] cyc=%0d also", $time, cyc);
      end
      else if (cyc == 17) begin
         $fstrobeb(fd, cyc, "b");
      end
      else if (cyc == 18) begin
         $fstrobeh(fd, cyc, "h");
      end
      else if (cyc == 19) begin
         $fstrobeo(fd, cyc, "o");
      end
      else if (cyc == 22) begin
         $fstrobe(fd, "[%0t] cyc=%0d new-strobe", $time, cyc);
      end
      else if (cyc == 24) begin
         $monitoroff;
      end
      else if (cyc == 26) begin
         $monitoron;
      end
      else if (cyc == 27) begin
         $fclose(fd);
      end
      else if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
