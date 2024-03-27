// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;

   bit clock = 1'b0;
   bit reset = 1'b0;

   initial begin
      $assertkill;

      #10

      reset = 1'b1;
      $display("%t: deassert reset %d", $time, reset);

      #40

      $asserton;

      reset = 1'b0;
      $display("%t: deassert reset %d", $time, reset);

      #200

      $display("%t: finish", $time);
      $write("*-* All Finished *-*\n");
      $finish;

   end

   always #10 clock = ~clock;
   reg r = 1'b0;

   always @(posedge clock) if (reset) r <= 1'b1;

   assert_test:
      assert property (@(posedge clock) (reset | r))
      else $error("%t: assertion triggered", $time);

endmodule
