// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define check(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: %m: Wrong parameter value\n", `__FILE__,`__LINE__); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   u u ();
   tx x ();

   parameter PARAM = 0;
   parameter HIER = 0;
   initial begin
      $display("%m PARAM=%0d HIER=%0d", PARAM, HIER);
`ifdef IVERILOG
      `check(PARAM, 0);
`elsif NC
      `check(PARAM, 0);
`elsif VCS
      `check(PARAM, 10);
`else
      `check(PARAM, 10);
`endif

      `check(HIER, 0);
   end
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module u;
   ux x();
endmodule

module ux;
   parameter PARAM = 0;
   parameter HIER = 0;
   initial begin
      $display("%m PARAM=%0d HIER=%0d", PARAM, HIER);
`ifdef IVERILOG
      `check(PARAM, 0);
`elsif NC
      `check(PARAM, 0);
`elsif VCS
      `check(PARAM, 10);
`else
      `check(PARAM, 0);
`endif
      `check(HIER, 0);
   end
endmodule

module tx;
   parameter PARAM = 0;
   parameter HIER = 0;
   initial begin
      $display("%m PARAM=%0d HIER=%0d", PARAM, HIER);
`ifdef IVERILOG
      `check(PARAM, 0);
`elsif NC
      `check(PARAM, 10);
`elsif VCS
      `check(PARAM, 10);
`else
      `check(PARAM, 0);
`endif
`ifdef NC
      `check(HIER, 20);
`else
      `check(HIER, 0);
`endif
   end
endmodule
