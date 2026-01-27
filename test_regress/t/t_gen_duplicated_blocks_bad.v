// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
   parameter X = 2;
   begin : block
   end
   begin : block
   end
   if (X > 0) begin : block1
   end
   if (X > 1) begin : block1
   end
endmodule
