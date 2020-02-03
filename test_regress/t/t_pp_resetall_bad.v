// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

`resetall  // Ok
module t;
`resetall  // Bad
endmodule
`resetall  // Ok
