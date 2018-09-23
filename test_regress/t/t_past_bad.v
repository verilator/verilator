// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Wilson Snyder.

module t (d, clk);
   input d;
   input clk;

   always @ (posedge clk) begin
      if ($past(d, 0)) $stop;  // IEEE 16.9.3 must be >- 0
      if ($past(d, 10000)) $stop;  // TICKCOUNT
   end
endmodule
