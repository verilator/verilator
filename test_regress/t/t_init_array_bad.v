// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional transitive alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0
//

module t;
    bit [7:0] r[3] = {{8'h1, 8'h2}, 8'h5};
    initial $finish;
endmodule
