// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

module t
  (
   input wire clk
   );

   integer    cyc; initial cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
   end
endmodule
