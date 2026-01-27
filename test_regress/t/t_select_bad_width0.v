// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   parameter int ZERO = 0;

   initial begin
      bit [31:0] val = '1;
      int left = 4;

      int part = val[left +: ZERO];
      $display(part);
      part = val[left -: ZERO];
      $display(part);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
