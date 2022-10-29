// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   event e;

   initial begin
       int x;
       #1
       fork @e; @e; join;
       @e
       wait(x == 4)
       x = #1 8;
       if (x != 8) $stop;
       if ($time != 0) $stop;
       @e
       if (!e.triggered) $stop;
       if ($time != 1) $stop;
       $write("*-* All Finished *-*\n");
       $finish;
   end

   initial #1 ->e;
   initial #2 $stop; // timeout
endmodule

`ifdef VERILATOR_TIMING
`error "VERILATOR_TIMING should not be defined with --no-timing"
`endif
