// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

`include "verilated.v"

module t;

   // Note $sscanf already tested elsewhere

   reg [3:0] n;
   reg [63:0] q;
   reg [16*8:1] wide;

   reg [8:1] 	char;
   reg [48*8:1] str;
   reg [48*8:1] str2;

   real 	r;

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

      $swrite(str2, "e=%e", r);
      $swrite(str2, "e=%f", r);
      $swrite(str2, "e=%g", r);

      r = 0.01;
      $swrite(str2, "e=%e f=%f g=%g", r, r, r);
`ifdef TEST_VERBOSE  $display("str2=%0s",str2);  `endif
      if (str2 !== "e=1.000000e-02 f=0.010000 g=0.01") $stop;

      $swrite(str2, "mod=%m");
`ifdef TEST_VERBOSE  $display("str2=%0s",str2);  `endif
`ifdef verilator
      if (str2 !== "mod=top.v") $stop;
`else
      if (str2 !== "mod=top.t") $stop;
`endif

      $sformat(char,"%s","c");
      if (char != "c") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
