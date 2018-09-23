// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Wilson Snyder.

module t (d, clk);
   input d;
   input clk;

   always @ (posedge clk) begin
      // Unsupported
      if ($past(d, 0, 0, 0)) $stop;
   end
endmodule
