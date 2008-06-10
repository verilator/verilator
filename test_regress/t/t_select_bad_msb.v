// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003-2007 by Wilson Snyder.

module t (clk);
   input clk;

   reg [43:0] mi;
   reg [3:0]  sel2;
   reg [0:22] backwd;

   always @ (posedge clk) begin
      mi = 44'h123;
      sel2 = mi[1:4];
      $write ("Bad select %x\n", sel2);
   end
endmodule
