// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   localparam int CHECKLIST_P [2:0] = '{0, 1, 2};

   localparam HIT_LP = 1;
   localparam MISS_LP = 4;
   localparam HIT_INSIDE = HIT_LP inside {CHECKLIST_P};
   localparam MISS_INSIDE = MISS_LP inside {CHECKLIST_P};

   initial begin
      if (HIT_INSIDE != 1) $stop;
      if (MISS_INSIDE != 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
