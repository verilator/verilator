// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkb(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='b%x exp='b%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);;

class Cls;
   int i;
endclass

module t;
   initial begin
      begin
         int q1[$];
         bit[31:0] q2[$];
         q1.push_back(1);
         q2.push_back(1);
         q1.push_back(-2);
         q2.push_back(-2);
         // Two checks because == and != may not be derived from each other
         `checkb(q1 == q2, 1'b1)
         `checkb(q1 != q2, 1'b0)

         q2.push_back(3);
         `checkb(q1 != q2, 1'b1)
         `checkb(q1 == q2, 1'b0)
      end
      begin
         string q1[$];
         string q2[$];
         q1.push_back("one");
         q2.push_back("one");
         q1.push_back("two");
         q2.push_back("two");
         `checkb(q1 == q2, 1'b1)
         `checkb(q1 != q2, 1'b0)

         q2.push_back("three");
         `checkb(q1 != q2, 1'b1)
         `checkb(q1 == q2, 1'b0)
      end

      begin
         Cls a = new;
         Cls b = new;
         Cls q1[$];
         Cls q2[$];
         q1.push_back(a);
         q2.push_back(b);
         `checkb(q1 != q2, 1'b1)
         `checkb(q1 == q2, 1'b0)

         q1.push_back(b);
         q2.push_front(a);
         `checkb(q1 == q2, 1'b1)
         `checkb(q1 != q2, 1'b0)
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
