// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
      clk
   );

   input clk;

   labeled_imas: assert #1 (clk);  // BAD: #1

endmodule
