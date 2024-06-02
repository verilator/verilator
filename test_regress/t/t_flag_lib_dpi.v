// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Shupei Fan.
// SPDX-License-Identifier: CC0-1.0

import "DPI-C" function void write_all_finished();

module t (/*AUTOARG*/);

   initial begin
      write_all_finished;
      $finish;
   end

endmodule
