// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2018 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import "DPI-C" dpii_sys_task = function void \$dpii_sys ();
import "DPI-C" dpii_failure = function int \$dpii_failure ();

module t (clk);
   input clk;
   integer cyc;
   integer failure;

   initial cyc = 0;

`ifndef verilator
   `error "Only Verilator supports PLI-ish DPI calls."
`endif

   always @ (posedge clk) begin
      if (cyc == 2) begin
         failure = $dpii_failure();
         $write("* failure = %0d\n", failure);
         if (failure > 0) begin
            $stop;
         end
         $write("*-* All Finished *-*\n");
         $finish;
      end
      cyc <= cyc + 1;
   end

   // The purpose of this test is to confirm that the DPI-call serialization
   // code in V3Partition does ensure that these DPI calls do not run
   // concurrently.
   //
   // Alternatively, the test may be run with "--threads-dpi all" in which case
   // it should confirm that the calls do run concurrently and do detect a
   // collision (they should, if the test is set up right.)  This is
   // t_dpi_threads_collide.pl.
   //
   // Q) Is it a risk that the partitioner will merge or serialize these always
   //    blocks, just by luck, even if the DPI-call serialization code fails?
   //
   // A) Yes, that's why t_dpi_threads_collide.pl also passes
   //    --no-threads-do-coaren to disable MTask coarsening.  This ensures that
   //    the MTask graph at the end of FixDataHazards (where we resolve DPI
   //    hazards) is basically the final MTasks graph, and that data hazards
   //    which persist beyond FixDataHazards should persist in the final
   //    generated C code.

   always @ (posedge clk) begin
      $dpii_sys();
   end

   always @ (posedge clk) begin
      $dpii_sys();
   end

endmodule
