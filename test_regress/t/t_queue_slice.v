// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);
   initial begin
      string q[$];
      string v;
      int    i;
      int    qi[$:5];
      int    ri[$];

      q.push_front("non-empty");
      i = q.size(); `checkh(i, 1);
      v = $sformatf("%p", q); `checks(v, "'{\"non-empty\"} ");

      q = '{};
      i = q.size(); `checkh(i, 0);

      q = '{"q"};
      v = $sformatf("%p", q); `checks(v, "'{\"q\"} ");

      q = {};
      i = q.size(); `checkh(i, 0);

      q = '{"q", "b", "c", "d", "e", "f"};
      if (q[0] !== "q") $stop;
      v = $sformatf("%p", q); `checks(v, "'{\"q\", \"b\", \"c\", \"d\", \"e\", \"f\"} ");

      q = {"q", "b", "c", "d", "e", "f"};
      v = $sformatf("%p", q); `checks(v, "'{\"q\", \"b\", \"c\", \"d\", \"e\", \"f\"} ");

      q.delete(1);
      v = q[1]; `checks(v, "c");
      v = $sformatf("%p", q); `checks(v, "'{\"q\", \"c\", \"d\", \"e\", \"f\"} ");

      q.insert(0, "ins0");
      q.insert(2, "ins2");
      v = q[0]; `checks(v, "ins0");
      v = q[2]; `checks(v, "ins2");
      v = $sformatf("%p", q); `checks(v, "'{\"ins0\", \"q\", \"ins2\", \"c\", \"d\", \"e\", \"f\"} ");

      // Slicing
      q = '{"q", "b", "c", "d", "e", "f"};
      q = q[-1:0];
      v = $sformatf("%p", q); `checks(v, "'{\"q\"} ");
      q = '{"q", "b", "c", "d", "e", "f"};
      q = q[2:3];
      v = $sformatf("%p", q); `checks(v, "'{\"c\", \"d\"} ");
      q = '{"q", "b", "c", "d", "e", "f"};
      q = q[3:$];
      v = $sformatf("%p", q); `checks(v, "'{\"d\", \"e\", \"f\"} ");
      q = q[$:$];
      v = $sformatf("%p", q); `checks(v, "'{\"f\"} ");

      // Similar using implied notation
      q = '{"f"};
      q = {q, "f1"};  // push_front
      q = {q, "f2"};  // push_front
      q = {"b1", q};  // push_back
      q = {"b2", q};  // push_back
      v = $sformatf("%p", q); `checks(v, "'{\"b2\", \"b1\", \"f\", \"f1\", \"f2\"} ");

      q = {q[0], q[2:$]};  // delete element 1
      v = $sformatf("%p", q); `checks(v, "'{\"b2\", \"f\", \"f1\", \"f2\"} ");

      q = {"a", "b"};
      q = {q, q};
      v = $sformatf("%p", q); `checks(v, "'{\"a\", \"b\", \"a\", \"b\"} ");

      begin
         string ai[$] = '{ "Foo", "Bar" };
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

      begin
         qi.push_back(0);
         qi.push_back(1);
         qi.push_back(2);
         qi.push_back(3);
         qi.push_back(4);
         qi.push_back(5);

         // Assignment to unsized queue from sized queue
         ri = qi[ 2 : 4 ];
         `checkh(ri.size, 3);
         ri = qi[ 4 : 2 ];
         `checkh(ri.size, 0);
         ri = qi[ 2 : 2 ];
         `checkh(ri.size, 1);
         ri = qi[ -2 : 2 ]; // 2 - 0 + 1 = 3
         `checkh(ri.size, 3);
         ri = qi[ 2 : 10 ]; // 5 - 2 + 1 = 4
         `checkh(ri.size, 4);

         // Assignment from unsized to sized
         ri = '{1,2,3,4,5,6,7,8,9};
         qi = ri;
         `checkh(qi.size, 5);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
