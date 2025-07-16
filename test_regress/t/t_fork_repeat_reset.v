// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   logic  clock;

   initial begin
      clock = '0;
      forever begin
         clock = #5ns ~clock;
      end
   end

   task static has_fork_task(input [31:0] address);
      @(posedge clock);
      fork
         begin
            repeat($urandom_range(9)) @(posedge clock);
         end
      join
   endtask

   // Intentionally created a recursive task chain (that should be unreachable anyway):
   // call_task()
   //   --> (unreachable) --> calls local_sub_task()
   //       --> calls call_task()
   //             --> ...
   //   --> (reachable) --> calls has_fork_task() done.

   task static call_task(input [31:0] address);
      if (1) begin
         // Workaround1: Comment this out to pass the compile.
         has_fork_task(address);
      end
      else begin
         // Workaround2: Comment this out to pass the compile
         // Should be unreachable anyway.
         local_sub_task(.address(address));
      end
   endtask

   task static local_sub_task(input [31:0] address);
      logic [63:0] req;
      logic [39:0] resp;
      req = '0;
      call_task(.address(32'h0000_1234));
      resp = '0;
   endtask

   initial begin : main
      #100ns;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
