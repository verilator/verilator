// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Michael Lefebvre.


module t(/*AUTOARG*/);

localparam int unsigned A2 [1:0] = '{5,6};
localparam int unsigned A3 [2:0] = '{4,5,6};

// Matching sizes with slicesel are okay.
localparam int unsigned B22 [1:0] = A2[1:0];
localparam int unsigned B33 [2:0] = A3[2:0];

// bug #3186
localparam int unsigned B32_B [1:0] = A3[1:0];
localparam int unsigned B32_T [1:0] = A3[2:1];

endmodule
