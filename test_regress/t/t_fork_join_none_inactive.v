// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
  initial
  fork
    #0 $write("This should be last\n");
    begin
      fork
        $write("This should be second\n");
      join_none
      $write("This should be first\n");
    end
  join_none
endmodule
