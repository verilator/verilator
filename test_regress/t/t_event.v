// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(args) $write args
`else
 `define WRITE_VERBOSE(args)
`endif

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   event e1;
   event e2;
`ifndef IVERILOG
   event ev [3:0];
`endif

   int   cyc = 0;

   int last_event = 0;
   always @(e1) begin
      `WRITE_VERBOSE(("[%0t] e1\n", $time));
      if (!e1.triggered) $stop;
      last_event[1] = 1;
   end

   always @(e2) begin
      `WRITE_VERBOSE(("[%0t] e2\n", $time));
      last_event[2] = 1;
   end

   always @(posedge clk) begin
      `WRITE_VERBOSE(("[%0t] cyc=%0d last_event=%5b\n", $time, cyc, last_event));
      cyc <= cyc + 1;
      if (cyc == 1) begin
         // Check no initial trigger
         if (last_event != 0) $stop;
      end
      //
      else if (cyc == 10) begin
         last_event = 0;
         -> e1;
      end
      else if (cyc == 12) begin
         if (last_event != 32'b10) $stop;
         last_event = 0;
      end
      else if (cyc == 13) begin
         // Check not still triggering
         if (last_event != 0) $stop;
         last_event = 0;
      end
      //
      else if (cyc == 10) begin
         last_event = 0;
         ->> e2;
      end
      else if (cyc == 12) begin
         if (last_event != 32'b100) $stop;
         last_event = 0;
      end
      else if (cyc == 13) begin
         // Check not still triggering
         if (last_event != 0) $stop;
         last_event = 0;
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
