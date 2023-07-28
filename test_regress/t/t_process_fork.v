// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   process job[] = new [8];

   initial begin
      foreach (job[j]) fork
         begin
            $write("job started\n");
            job[j] = process::self();
         end
      join_none
      foreach (job[j]) begin
         wait (job[j]);
      end
      $write("all jobs started\n");
      foreach (job[j]) begin
         job[j].await();
      end
      $write("all jobs finished\n");
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
