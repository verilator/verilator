// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   integer i;
   initial begin
      $unknown_pli_task;
      $unknown_pli_task("arg", i);
      i = $unknown_pli_function;
      i = $unknown_pli_function("arg", i);

      $sformatff();  // Typo
      i = $sformatff();  // Typo

      $stop;
   end
endmodule
