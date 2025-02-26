// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

    wire clk;

    let letf(x) = (x << 1);

    always @(posedge clk) begin
        case (0)
          0: letf(0); // Bad, need a statement
        endcase
    end

endmodule
