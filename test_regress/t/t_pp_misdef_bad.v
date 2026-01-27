// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2004 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
`define DEFINED

   // NDEFINED isn't defined here:
   `NDEFINED

     // Botched directive (`timescale)
     `imescale

     initial $stop; // Should have failed

endmodule
