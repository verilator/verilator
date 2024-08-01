// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t(/*AUTOARG*/);

   int qdel[$];
   int qkept[$];

   task automatic func(ref int vrefed);
`ifdef TEST_NOINLINE
      // verilator no_inline_task
`endif
      `checkd(vrefed, 2);
      #100;
      vrefed = 10;
      #10;
      `checkd(vrefed, 10);
   endtask

   initial begin
      qkept.push_back(1);
      qkept.push_back(2);
      qkept.push_back(3);
      qdel = qkept;
      $display("qkept=%p  qdel=%p", qkept, qdel);
      `checkd(qkept[0], 1);
      `checkd(qkept[1], 2);
      `checkd(qkept[2], 3);

      func(qdel[1]);
      func(qkept[1]);

      $display("qkept=%p  qdel=%p", qkept, qdel);
      `checkd(qdel.size, 0);
      `checkd(qkept[0], 1);
      `checkd(qkept[1], 10);
      `checkd(qkept[2], 3);
   end

   initial begin
      #50;
      `checkd(qdel[1], 2);
      `checkd(qkept[1], 2);
      qdel.delete();
      #100;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
