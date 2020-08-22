// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_lint_declfilename_bbox ();
   parameter IN = 0;
   if (IN) begin
      // Should not warn, see bug2430
      BLACKBOXED bboxed ();
   end
endmodule
