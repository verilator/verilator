// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "verilated.v"

module t;

   // Note $sscanf already tested elsewhere

   reg [3:0] n;
   reg [63:0] q;
   reg [16*8:1] wide;

   reg [8:1]    ochar;
   reg [48*8:1] str;
   reg [48*8:1] str2;
   string str3;


   real         r;

   initial begin
      n = 4'b1100;
      q = 64'h1234_5678_abcd_0123;
      wide = "hello-there12345";
      $sformat(str, "n=%b q=%d w=%s", n, q, wide);
`ifdef TEST_VERBOSE  $display("str=%0s",str);  `endif
      if (str !== "n=1100 q= 1311768467750060323 w=hello-there12345") $stop;

      q = {q[62:0],1'b1};
      $swrite(str2, "n=%b q=%d w=%s", n, q, wide);
`ifdef TEST_VERBOSE  $display("str2=%0s",str2);  `endif
      if (str2 !== "n=1100 q= 2623536935500120647 w=hello-there12345") $stop;

      str3 = $sformatf("n=%b q=%d w=%s", n, q, wide);
`ifdef TEST_VERBOSE  $display("str3=%0s",str3);  `endif
      if (str3 !== "n=1100 q= 2623536935500120647 w=hello-there12345") $stop;

      $swrite(str2, "e=%e", r);
      $swrite(str2, "e=%f", r);
      $swrite(str2, "e=%g", r);

      r = 0.01;
      $swrite(str2, "e=%e f=%f g=%g", r, r, r);
`ifdef TEST_VERBOSE  $display("str2=%0s",str2);  `endif
      if (str2 !== "e=1.000000e-02 f=0.010000 g=0.01") $stop;

      $swrite(str2, "mod=%m");
`ifdef TEST_VERBOSE  $display("str2=%0s",str2);  `endif
      if (str2 !== "mod=top.t") $stop;

      $swrite(str2, "lib=%l");
`ifdef TEST_VERBOSE  $display("chkl %0s",str2);  `endif
      if (str2 !== "lib=t") $stop;

      str3 = $sformatf("u=%u", {"a","b","c","d"}); // Value selected so is printable
`ifdef TEST_VERBOSE  $display("chku %s %s",str3,str3);  `endif
      if (str3 !== "u=dcba") $stop;

      str3 = $sformatf("v=%v", {"a","b","c","d"}); // Value selected so is printable
`ifdef TEST_VERBOSE  $display("chkv %s %s",str3,str3);  `endif

      $sformat(ochar,"%s","c");
      if (ochar != "c") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
