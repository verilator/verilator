// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

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
         // Simple test using integer
         typedef bit [3:0] nibble_t;
         nibble_t q[$];
         nibble_t v;

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

         q.push_front("f1");
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

         v = q.pop_front(); `checks(v, "f2");
         v = q.pop_front(); `checks(v, "f1");
         v = q.pop_back(); `checks(v, "b2");
         v = q.pop_back(); `checks(v, "b1");
         i = q.size(); `checkh(i, 0);

         q.push_front("non-empty");
         i = q.size(); `checkh(i, 1);
         q.delete();
         i = q.size(); `checkh(i, 0);
         v = q.pop_front(); `checks(v, "");  // Was empty, optional warning
         v = q.pop_back(); `checks(v, "");  // Was empty, optional warning

         // COnversion of insert/delete with zero to operator
         q.push_front("front");
         q.insert(0, "newfront");
         i = q.size(); `checkh(i, 2);
         q.delete(0);
         i = q.size(); `checkh(i, 1);
         `checks(q[0], "front");

      end

      // See t_queue_unsup_bad for more unsupported stuff

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
