// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   event e1;
   event e2;
   event e3;
   initial forever begin
      #2
      ->e1;
      #2
      ->e2;
      #2
      ->e3;
   end
   initial begin
      for (int i = 0; i < 10; i++) begin
          @(e1, e2, e3)
          if (!e1.triggered && !e2.triggered && !e3.triggered) $stop;
`ifdef TEST_VERBOSE
          $write("got event %0d\n", i);
`endif
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

   initial #21 $stop; // timeout
endmodule

`ifndef VERILATOR_TIMING
`error "VERILATOR_TIMING should have been defined as have --timing"
`endif
