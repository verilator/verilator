// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

/// We define the modules in "backward" order.

module d;
endmodule

module b;
   generate if (1) begin
      c c1 ();
      c c2 ();
   end
   endgenerate
endmodule

module c;
   generate if (1) begin
      d d1 ();
      d d2 ();
   end
   endgenerate
endmodule

module a;
   generate if (1) begin
      b b1 ();
      b b2 ();
   end
   endgenerate
endmodule

module t (/*AUTOARG*/);

   a a1 ();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
