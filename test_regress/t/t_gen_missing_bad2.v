// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   if ($test$plusargs("BAD-non-constant")) begin
      initial $stop;
   end
   case (1)
      $test$plusargs("BAD-non-constant"): initial $stop;
   endcase

endmodule
