// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Michael Lefebvre.


module t(/*AUTOARG*/);

localparam int unsigned A3 [2:0] = '{4,5,6};

// slicesel out of range should fail
localparam int unsigned B32_T [1:0] = A3[3:1];

endmodule
