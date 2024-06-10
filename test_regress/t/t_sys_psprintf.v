// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;

   // Note $sformatf already tested elsewhere

   reg [3:0] n;
   reg [63:0] q;
   reg [16*8:1] wide;

   string str;

   initial begin
      n = 4'b1100;
      q = 64'h1234_5678_abcd_0123;
      wide = "hello-there12345";
      str = $psprintf("n=%b q=%d w=%s", n, q, wide);
`ifdef TEST_VERBOSE  $display("str=%0s",str);  `endif
      if (str !== "n=1100 q= 1311768467750060323 w=hello-there12345") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
