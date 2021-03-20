// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   if (1) begin
      $info;
      $info("User elaboration-time info");
      $warning;
      $warning("User elaboration-time warning");
      $warning(1);  // Check can convert arguments to format
      $error;
      $error("User elaboration-time error");
      $fatal(0, "User elaboration-time fatal");
   end

endmodule
