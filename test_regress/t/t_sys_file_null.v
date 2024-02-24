// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
   integer fd, cnt;
   initial begin
      fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR),"/zeros.log"}, "w");
      for (cnt = 0; cnt < 16; cnt = cnt + 4)
        $fwrite(fd, "%u", 32'd0);
      $fclose(fd);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
