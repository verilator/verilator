// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t ();

   // This shows the uglyness in width warnings across param modules
   // TODO: Would be nice to also show relevant parameter settings
   p #(.WIDTH(4)) p4 (.in(4'd0));
   p #(.WIDTH(5)) p5 (.in(5'd0));

endmodule

module p
  #(parameter WIDTH=64)
   (input [WIDTH-1:0] in);
   wire [4:0] out = in;
endmodule
