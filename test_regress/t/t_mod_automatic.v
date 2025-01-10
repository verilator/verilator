// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module automatic t(/*AUTOARG*/);

   task static accum_s(input integer value, output integer result);
      static int acc = 1;
      acc = acc + value;
      result = acc;
   endtask

   task accum_a(input integer value, output integer result);
      int acc = 1;  // automatic
      acc = acc + value;
      result = acc;
   endtask

   integer value;

   reg failed = 0;  // Static

   initial begin
      accum_s(2, value);
      $display("%d", value);
      if (value !== 3) failed = 1;

      accum_s(3, value);
      $display("%d", value);
      if (value !== 6) failed = 1;

      accum_a(2, value);
      $display("%d", value);
      if (value !== 3) failed = 1;

      accum_a(3, value);
      $display("%d", value);
      if (value !== 4) failed = 1;

      if (failed) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
