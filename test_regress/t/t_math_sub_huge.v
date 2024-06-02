// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(
    input clk,
    input [2559:0] pkt_data,
    output reg [15:0] vlan
);

    always @(posedge clk) begin
       vlan <= pkt_data[{308, 3'b0} - 1 -: 16];
    end

endmodule
