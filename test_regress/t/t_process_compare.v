// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class A;
   local process proc2;
   task run;
      process proc1;
      proc1 = process::self();

      if (proc2 == null) begin
         proc2 = proc1;
      end
      else if (proc1 == proc2) begin
         $display("process is equal %p %p", proc1, proc2);
      end
      else begin
         $display("process is not equal (using ! ==) %p %p", proc1, proc2);
         $stop;
      end

      if (proc2 != null && proc1 != proc2) begin
         $display("process is not equal (using !=) %p %p", proc1, proc2);
         $stop;
      end
   endtask
endclass

module t;
   initial begin
      A a;
      a = new();
      a.run();
      a.run();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
