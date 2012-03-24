// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Lane Brooks.

module t (clk);
   input clk;

   wire  A;
   
   pullup p1(A);
   pulldown p2(A);

endmodule
