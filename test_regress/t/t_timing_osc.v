// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module tb_osc;

   timeunit 1s;
   timeprecision 1fs;

   logic dco_out;

   bhv_dco dco (
                // Inputs
                .coarse_cw(8.0),
                .medium_cw(8.0),
                .fine_cw(32.0),

                // Outputs
                .rf_out(dco_out)
                );

   initial begin
      $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
      $dumpvars;
`ifdef TEST_BENCHMARK
      #200ns;
`else
      #3ns;
`endif
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module bhv_dco (
                input real   coarse_cw,
                input real   medium_cw,
                input real   fine_cw,
                output logic rf_out
                );

   parameter realtime coarse_ofst = 600ps;
   parameter realtime coarse_res  = 60ps;
   parameter realtime medium_ofst = 130ps;
   parameter realtime medium_res  = 6ps;
   parameter realtime fine_ofst   = 70ps;
   parameter realtime fine_res    = 0.2ps;

   timeunit 1s;
   timeprecision 1fs;

   realtime coarse_delay, medium_delay, fine_delay, jitter;
   assign coarse_delay = 0.5 * (coarse_cw * coarse_res + coarse_ofst         );
   assign medium_delay = 0.5 * (medium_cw * medium_res + medium_ofst         );
   assign   fine_delay = 0.5 * (  fine_cw *   fine_res +   fine_ofst + jitter);
   assign jitter = 0;

   logic    coarse_out, medium_out, fine_out;

   initial coarse_out = 0;
   always @ (fine_out) coarse_out <= #coarse_delay ~fine_out;
   assign #medium_delay medium_out = ~coarse_out;
   assign #fine_delay   fine_out   = ~medium_out;

   assign #50ps rf_out = fine_out;

endmodule
