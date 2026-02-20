// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Shupei Fan
// SPDX-License-Identifier: CC0-1.0

import "DPI-C" function void write_all_finished();

module t;

   initial begin
      write_all_finished;
      $finish;
   end

endmodule
