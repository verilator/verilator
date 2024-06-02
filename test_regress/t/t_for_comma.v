// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkc(expc) \
      do begin \
         if (c !== expc) begin \
            $write("%%Error: %s:%0d:  a=%0d b=%0d c=%0d expc=%0d\n", `__FILE__,`__LINE__, a, b, c, (expc)); \
            $stop; \
         end \
         a=0; b=0; c=0; \
      end while(0);

module t (/*AUTOARG*/);

   int a, b, c;

   initial begin
      for (; ; ) begin c = c + 1 + a + b; break; end
      `checkc(1);
      for (; ; a = a + 1) begin c = c + 1 + a + b; break; end
      `checkc(1);
      for (; ; a = a + 1, b = b + 1) begin c = c + 1 + a + b; break; end
      `checkc(1);
      for (; a < 3; ) begin c = c + 1 + a + b; break; end
      `checkc(1);
      for (; a < 3; a = a + 1) begin c = c + 1 + a + b; break; end
      `checkc(1);
      for (; a < 3; a = a + 1, b = b + 1) begin c = c + 1 + a + b; break; end
      `checkc(1);
      for (a = 1; a < 3; ) begin c = c + 1 + a + b; a = a + 10; end
      `checkc(2);
      for (a = 1; a < 3; a = a + 1) begin c = c + 1 + a + b; end
      `checkc(5);
      for (a = 1; a < 3; a = a + 1, b = b + 1) begin c = c + 1 + a + b; end
      `checkc(6);
      for (int a = 1; a < 3; ) begin c = c + 1 + a + b; a = a + 10; end
      `checkc(2);
      for (int a = 1; a < 3; a = a + 1) begin c = c + 1 + a + b; end
      `checkc(5);
      for (int a = 1; a < 3; a = a + 1, b = b + 1) begin c = c + 1 + a + b; end
      `checkc(6);
      for (var int a = 1; a < 3; ) begin c = c + 1 + a + b; a = a + 10; end
      `checkc(2);
      for (var int a = 1; a < 3; a = a + 1) begin c = c + 1 + a + b; end
      `checkc(5);
      for (var int a = 1; a < 3; a = a + 1, b = b + 1) begin c = c + 1 + a + b; end
      `checkc(6);
      for (int a = 1, int b = 1; a < 3; ) begin c = c + 1 + a + b; a = a + 10; end
      `checkc(3);
      for (int a = 1, int b = 1; a < 3; a = a + 1) begin c = c + 1 + a + b; end
      `checkc(7);
      for (int a = 1, int b = 1; a < 3; a = a + 1, b = b + 1) begin c = c + 1 + a + b; end
      `checkc(8);
      for (int a = 1, x = 1; a < 3; a = a + 1, x = x + 1) begin c = c + 1 + a + x; end
      `checkc(8);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
