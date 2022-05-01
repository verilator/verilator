// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   integer cyc; initial cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         ReadContDisps;
      end
      else if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
`ifndef verilator
      DispContDisps;
`endif
   end

   task ReadContDisps;
      begin
         $display("%m: Here: %d", cyc);
      end
   endtask

   integer dindex;

   task DispContDisps;
      /* verilator public */
      begin
         if (cyc >= 2) begin
            if ( cyc >= 4 ) begin
               dindex = dindex + 2; //*** Error line
               $display("%m: DIndex increment %d", cyc);
`ifdef VERILATOR
               $c("VL_PRINTF(\"Hello1?\\n\");");
`endif
            end
`ifdef VERILATOR
            $c("VL_PRINTF(\"Hello2?\\n\");");
            $c("VL_PRINTF(\"Hello3?\\n\");");
`endif
         end
      end
   endtask

endmodule
