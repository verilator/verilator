// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Wilson Snyder.

module t ();

   initial begin
      forever begin end
      // verilator lint_off UNSIGNED
      for (reg [31:0] i=0; i>=0; i=i+1) begin end
   end
endmodule
