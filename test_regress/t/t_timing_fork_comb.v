// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic clk = 0;

   assign #5 clk = ~clk;

   int a = 0;
   always @(posedge clk) begin
       a <= a + 1;
`ifdef TEST_VERBOSE
       $display("a=%0d, b=%0d, c=%0d, d=%0d, e=%0d, f=%0d, v=%b", a, b, c, d, e, f, v);
`endif
   end

   int b = 0, c = 0, d = 0, e = 0, f = 0;
   always @a begin
       b = a << 1;
       fork
           #10 d = b + c;
           e = c + d;
           #5 f = d + e;
       join_none
       c = a + b;
   end

   logic[5:0] v;
   always @a begin
       v[0] = a[0];
       fork
           begin
               v[1] = a[1];
               #5 v[2] = a[2];
           end
           #10 v[3] = a[3];
       join_none
       v[4] = a[4];
   end

   initial #100 begin
`ifdef TEST_VERBOSE
       $display("a=%0d, b=%0d, c=%0d, d=%0d, e=%0d, f=%0d, v=%b", a, b, c, d, e, f, v);
`endif
       if (a != 10) $stop;
       if (b != 20) $stop;
       if (c != 30) $stop;
       if (d != 45) $stop;
       if (e != 75) $stop;
       if (f != 107) $stop;
       if (v != 'b001010) $stop;
       $write("*-* All Finished *-*\n");
       $finish;
   end
endmodule
