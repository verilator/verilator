// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkg(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%g' exp='%g'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);
   initial begin
      string q[$];
      string v;
      int    i;

      q.push_front("non-empty");
      i = q.size(); `checkh(i, 1);
      v = $sformatf("%p", q); `checks(v, "'{\"non-empty\"} ");

      q = '{"q", "b", "c", "d", "e", "f"};
      v = $sformatf("%p", q); `checks(v, "'{\"q\", \"b\", \"c\", \"d\", \"e\", \"f\"} ");

      q = {"q", "b", "c", "d", "e", "f"};
      v = $sformatf("%p", q); `checks(v, "'{\"q\", \"b\", \"c\", \"d\", \"e\", \"f\"} ");

      q.delete(1);
      v = q[1]; `checks(v, "c");

      q.insert(0, "ins0");
      q.insert(2, "ins2");
      v = q[0]; `checks(v, "ins0");
      v = q[2]; `checks(v, "ins2");
      v = $sformatf("%p", q); `checks(v, "'{\"ins0\", \"q\", \"ins2\", \"c\", \"d\", \"e\", \"f\"} ");

      // Slicing
      q = {"q", "b", "c", "d", "e", "f"};
      q = q[2:3];
      v = $sformatf("%p", q); `checks(v, "'{\"c\", \"d\"} ");
      q = {"q", "b", "c", "d", "e", "f"};
      q = q[3:$];
      v = $sformatf("%p", q); `checks(v, "'{\"d\", \"e\", \"f\"} ");

      // Similar using implied notation
      q = {q, "f1"};  // push_front
      q = {q, "f2"};  // push_front
      q = {"b1", q};  // push_back
      q = {"b2", q};  // push_back
      q = {q[0], q[2:$]};  // delete element 1
      v = $sformatf("%p", q); `checks(v, "'{\"b2\", \"d\", \"e\", \"f\", \"f1\", \"f2\"} ");

      begin
         string ai[$] = { "Foo", "Bar" };
         q = ai;  // Copy
         i = q.size(); `checkh(i, 2);
         v = q.pop_front(); `checks(v, "Foo");
         v = q.pop_front(); `checks(v, "Bar");
         q = '{ "BB", "CC" };  // Note '{} not {}
         v = q.pop_front(); `checks(v, "BB");
         v = q.pop_front(); `checks(v, "CC");
         q = { "BB", "CC" };  // Note {} not '{}
         v = q.pop_front(); `checks(v, "BB");
         v = q.pop_front(); `checks(v, "CC");
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
