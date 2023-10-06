// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

    function automatic real logWrapper(real x);
      return $ln(x);
    endfunction

    function automatic void showError();
         $display("bad int cast");
         $display("x=%f, y=%f", logWrapper( real'(10)), 1.0 * logWrapper( real'(10)));
         for (int i = 1; i < 10; i++) begin
            $display("x=%f, y=%f", logWrapper(real'(i)), 1.0 * logWrapper(real'(i)));
         end
         $display("no cast");
         for (int i = 1; i < 10; i++) begin
            $display("x=%f, y=%f", $ln(real'(i)), 1.0 * $ln(real'(i)));
         end
    endfunction


   initial begin

      showError();

      if (logWrapper( real'(10)) !=  1.0 * logWrapper( real'(10))) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
