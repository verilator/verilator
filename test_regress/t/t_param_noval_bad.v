// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t #(parameter P);
   generate
      var j;
      for (j=0; P; j++)
        initial begin end
   endgenerate
endmodule
