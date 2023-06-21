// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

localparam UADDR_WIDTH = 4'd10;
localparam UROM_WIDTH = 5'd17;
localparam UROM_DEPTH = 11'd1024;


module t(
         input clk,
         input [UADDR_WIDTH-1:0] mAddr,
         output logic [UROM_WIDTH-1:0] mOutput);

   reg [UROM_WIDTH-1:0] uRam[UROM_DEPTH];

   always @(posedge clk) mOutput <= uRam[mAddr];

endmodule
