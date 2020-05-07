// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkg(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%g' exp='%g'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc=0;

   integer i;

   always @ (posedge clk) begin
      cyc <= cyc + 1;

      begin
         // Very simple test using bit
         bit q[$];
         bit x;

         `checkh($left(q), 0);
         `checkh($right(q), -1);
         `checkh($increment(q), -1);
         `checkh($low(q), 0);
         `checkh($high(q), -1);
         `checkh($size(q), 0);
         `checkh($dimensions(q), 1);
         // Unsup: `checkh($bits(q), 0);

         q.push_back(1'b1);
         `checkh($left(q), 0);
         `checkh($right(q), 0);
         `checkh($increment(q), -1);
         `checkh($low(q), 0);
         `checkh($high(q), 0);
         `checkh($size(q), 1);
         `checkh($dimensions(q), 1);
         // Unsup: `checkh($bits(q), 2);
         `checkh(q.size(), 1);

         q.push_back(1'b1);
         q.push_back(1'b0);
         q.push_back(1'b1);
         `checkh($left(q), 0);
         `checkh($right(q), 3);
         `checkh($low(q), 0);
         `checkh($high(q), 3);
         `checkh($size(q), 4);
         // Unsup: `checkh($bits(q), 4);
         `checkh(q.size(), 4);

         x = q.pop_back(); `checkh(x, 1'b1);
         `checkh($left(q), 0);
         `checkh($right(q), 2);
         `checkh($low(q), 0);
         `checkh($high(q), 2);
         `checkh($size(q), 3);
         // sure those are working now..

         x = q.pop_front(); `checkh(x, 1'b1);
         x = q.pop_front(); `checkh(x, 1'b1);
         x = q.pop_front(); `checkh(x, 1'b0);
         `checkh(q.size(), 0);
      end

      begin
         // Simple test using integer
         typedef bit [3:0] nibble_t;
         nibble_t q[$];
         nibble_t v;

         `checkh($left(q), 0);
         `checkh($right(q), -1);
         `checkh($increment(q), -1);
         `checkh($low(q), 0);
         `checkh($high(q), -1);
         `checkh($size(q), 0);
         `checkh($dimensions(q), 2);

         i = q.size(); `checkh(i, 0);
         q.push_back(4'd1); // 1
         q.push_front(4'd2); // 2 1
         q.push_back(4'd3);  // 2 1 3
         i = q.size; `checkh(i, 3);  // Also checks no parens
      end

      begin
         // Strings
         string q[$];
         string v;
         int j = 0;

         // Empty queue checks
         `checkh($left(q), 0);
         `checkh($right(q), -1);
         `checkh($increment(q), -1);
         `checkh($low(q), 0);
         `checkh($high(q), -1);
         `checkh($size(q), 0);
         `checkh($dimensions(q), 2);
         //Unsup: `checkh($bits(q), 0);

         q.push_front("f1");

         //Unsup: `checkh($bits(q), 16);

         q.push_back("b1");
         q.push_front("f2");
         q.push_back("b2");
         i = q.size(); `checkh(i, 4);

         v = q[0]; `checks(v, "f2");
         v = q[1]; `checks(v, "f1");
         v = q[2]; `checks(v, "b1");
         v = q[3]; `checks(v, "b2");
         v = q[4]; `checks(v, "");

         v = $sformatf("%p", q); `checks(v, "'{\"f2\", \"f1\", \"b1\", \"b2\"} ");

         //Unsup: q.delete(1);
         //Unsup: v = q[1]; `checks(v, "b1");

         //Unsup: q.insert(0, "ins0");
         //Unsup: q.insert(3, "ins3");
         //v = q[0]; `checks(v, "ins0");
         //v = q[3]; `checks(v, "ins3");

         foreach (q[i]) begin
            j++;
            v = q[i];
            if (i == 0) `checks(v, "f2");
            if (i == 1) `checks(v, "f1");
            if (i == 2) `checks(v, "b1");
            if (i == 3) `checks(v, "b2");
         end
         `checkh(j,4);

         q.pop_front();
         v = q.pop_front(); `checks(v, "f1");
         v = q.pop_back(); `checks(v, "b2");
         v = q.pop_back(); `checks(v, "b1");
         i = q.size(); `checkh(i, 0);

         // Empty queue, this should be 0
         foreach (q[i]) begin
            j++;
         end
         `checkh(j,4);

         q.push_front("non-empty");
         i = q.size(); `checkh(i, 1);
         q.delete();
         i = q.size(); `checkh(i, 0);
         v = q.pop_front(); `checks(v, "");  // Was empty, optional warning
         v = q.pop_back(); `checks(v, "");  // Was empty, optional warning

         // Conversion of insert/delete with zero to operator
         q.push_front("front");
         q.insert(0, "newfront");
         i = q.size(); `checkh(i, 2);
         q.delete(0);
         i = q.size(); `checkh(i, 1);
         `checks(q[0], "front");

      end

      begin
         typedef struct packed {
            bit [7:0] opcode;
            bit [23:0] addr;
         } instruction; // named structure type

         instruction q[$];

         `checkh($dimensions(q), 2);
         //Unsup: `checkh($bits(q), 0);

      end

      /* Unsup:
      begin
         int q[4][$];

         q[0].push_back(0);
         q[0].push_back(1);
         q[1].push_back(2);
         q[2].push_back(3);

      end
      */

      // See t_queue_unsup_bad for more unsupported stuff

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
