// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface stream_ifc #(
) (
    input logic clk_i
);
endinterface

package pkg;
  class stream_driver #();
    virtual stream_ifc stream;
  endclass
endpackage

module t;
endmodule
