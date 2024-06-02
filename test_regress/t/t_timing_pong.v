// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   event ping;
   event pong;

   int cnt = 0;

   initial forever @ping begin
`ifdef TEST_VERBOSE
       $write("ping\n");
`endif
       cnt++;
       ->pong;
   end

   initial forever @pong begin
`ifdef TEST_VERBOSE
       $write("pong\n");
`endif
       if (cnt < 10) ->ping;
   end

   initial #1 ->ping;
   initial #2
       if (cnt == 10) begin
           $write("*-* All Finished *-*\n");
           $finish;
       end else $stop;
   initial #3 $stop;  // timeout
endmodule
