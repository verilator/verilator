// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   function automatic real logWrapper(real x);
      return $ln(x);
   endfunction

   initial begin
      // See bug4543
      $display("bad x=%f, y=%f", logWrapper(10.0), 1.0 * logWrapper(10.0));
      $display("noc x=%f, y=%f", $ln(10.0), 1.0 * $ln(10.0));
      if (logWrapper(10.0) != $ln(10.0)) $stop;
      if (logWrapper(10.0) != 1.0 * logWrapper(10.0)) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
