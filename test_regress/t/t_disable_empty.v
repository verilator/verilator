// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   initial begin
      if (0) begin : block
      end
      disable block;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
