// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t_lint_declfilename_bbox ();
   parameter IN = 0;
   if (IN) begin : gen_hasbbox
      // Should not warn, see bug2430
      BLACKBOXED bboxed ();
   end
endmodule
