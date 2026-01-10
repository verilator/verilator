// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface apb_if (
    input bit clk
);
  wire [31:0] paddr;
  wire [31:0] prdata;

  clocking mck @(posedge clk);
    output paddr;
    input prdata;

    // Some UVM tests declare this sequence but never use it
    // so we defer UNSUPPORTED until usage point
    sequence at_posedge;
      1;
    endsequence : at_posedge
  endclocking

endinterface

module t (
    input clk
);

  apb_if ifc (clk);

  initial $finish;

endmodule
