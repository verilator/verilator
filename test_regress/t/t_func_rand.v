// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2006 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (clk, Rand);
  input clk;
  output reg [31:0] Rand;

  function [31:0] QxRand32;
    input [7:0]    tbl;
    input [7:0]    idx;
    begin
`ifdef verilator
      // 'this' in $c must still refer to the module instance
      QxRand32 = $c("[&](unsigned int, unsigned int) { return this->vlNamep ? 0xfeed0fadU : 0U; }(",
                    tbl, ",", idx, ")");
`else
      QxRand32 = 32'hfeed0fad;
`endif
    end
  endfunction

  always @(posedge clk) begin
    Rand <= #1 QxRand32(8'h0, 8'h7);
    $display(Rand);
  end
endmodule
