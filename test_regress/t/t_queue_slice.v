// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

module t;
  initial begin
    typedef string q_t[$];
    q_t q;
    string v;
    int i;
    int qi[$:5];
    int ri[$];

    q.push_front("non-empty");
    i = q.size();
    `checkh(i, 1);
    `checkp(q, "'{\"non-empty\"}");

    q = '{};
    i = q.size();
    `checkh(i, 0);

    q = '{"q"};
    `checkp(q, "'{\"q\"}");

    q = {};
    i = q.size();
    `checkh(i, 0);

    q = '{"q", "b", "c", "d", "e", "f"};
    if (q[0] !== "q") $stop;
    `checkp(q, "'{\"q\", \"b\", \"c\", \"d\", \"e\", \"f\"}");

    q = {"q", "b", "c", "d", "e", "f"};
    `checkp(q, "'{\"q\", \"b\", \"c\", \"d\", \"e\", \"f\"}");

    q.delete(1);
    v = q[1];
    `checks(v, "c");
    `checkp(q, "'{\"q\", \"c\", \"d\", \"e\", \"f\"}");

    q.insert(0, "ins0");
    q.insert(2, "ins2");
    v = q[0];
    `checks(v, "ins0");
    v = q[2];
    `checks(v, "ins2");
    `checkp(q, "'{\"ins0\", \"q\", \"ins2\", \"c\", \"d\", \"e\", \"f\"}");

    // Slicing.

    // The simple cases:
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[2:3];
    `checkp(q, "'{\"c\", \"d\"}");
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[3:$];
    `checkp(q, "'{\"d\", \"e\", \"f\"}");

    // These are all the special cases straight from the LRM.  We
    // repeat tests for queues with size 1 specially because they are
    // tricky.

    // If a > b, then Q[a:b] yields the empty queue {}.
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[4:0];
    `checkp(q, "'{}");
    // FIX!
    // q = '{"q", "b", "c", "d", "e", "f"};
    // q = q[$:0];
    // `checkp(q, "'{}");
    q = '{"q"};
    q = q[1:0];
    `checkp(q, "'{}");
    // Or another way of writing the above (this case is specifically
    // described under section 7.10.4, Updating a queue using
    // assignment)
    q = '{"q"};
    q = q[1:$];
    `checkp(q, "'{}");


    // Q[ n : n ] yields a queue with one item, the one at position n
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[1:1];
    `checkp(q, "'{\"b\"}");
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[$:$];
    `checkp(q, "'{\"f\"}");
    // FIX!
    // q = '{"q"};
    // q = q[0:0];
    // `checkp(q, "'{\"q\"}");
    // FIX!
    // q = '{"q"};
    // q = q[0:$];
    // `checkp(q, "'{\"q\"}");
    // FIX!
    // q = '{"q"};
    // q = q[$:$];
    // `checkp(q, "'{\"q\"}");

    // If n lies outside Q’s range (n < 0 or n > $), then Q[n:n]
    // yields the empty queue {}
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[7:7];
    `checkp(q, "'{}");
    q = '{"q"};
    q = q[7:7];
    `checkp(q, "'{}");

    // If either a or b are 4-state expressions containing X or Z
    // values, it yields the empty queue {}
    // TODO: z not supported?
    // q = '{"q", "b", "c", "d", "e", "f"};
    // q = q['hz:3];
    // `checkp(q, "'{}");
    // TODO: z not supported?
    // q = '{"q", "b", "c", "d", "e", "f"};
    // q = q[3:'hz];
    // `checkp(q, "'{}");
    // FIX!
    // q = '{"q", "b", "c", "d", "e", "f"};
    // Q = q['hx:3];
    // `checkp(q, "'{}");
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[3:'hx];
    `checkp(q, "'{}");
    // TODO: z not supported?
    // q = '{"q"};
    // q = q['hz:0];
    // `checkp(q, "'{}");
    // TODO: z not supported?
    // q = '{"q"};
    // q = q[0:'hz];
    // `checkp(q, "'{}");
    q = '{"q"};
    q = q['bx:0];
    `checkp(q, "'{}");
    q = '{"q"};
    q = q[0:'bx];
    `checkp(q, "'{}");

    //  Q[ a : b ] where a < 0 is the same as Q[ 0 : b ]
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[-1:0];
    `checkp(q, "'{\"q\"}");
    q = '{"q"};
    q = q[-1:0];
    `checkp(q, "'{\"q\"}");

    // Q[ a : b ] where b > $ is the same as Q[ a : $ ]
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[3:7];
    `checkp(q, "'{\"d\", \"e\", \"f\"}");
    q = '{"q"};
    q = q[0:3];
    `checkp(q, "'{\"q\"}");

    // There isn't actually a clear statement in the LRM for when a >
    // $ and b > $, but in the same section as all the above rules it
    // says, "An invalid index value (i.e., a 4-state expression whose
    // value has one or more x or z bits, or a value that lies outside
    // 0...$) shall cause a read operation to return the value
    // appropriate for a nonexistent array entry of the queue’s
    // element type (as described in Table 7-1 in 7.4.6)"
    q = '{"q", "b", "c", "d", "e", "f"};
    q = q[6:8];
    `checkp(q, "'{}");
    q = '{"q"};
    q = q[6:8];
    `checkp(q, "'{}");

    // Similar using implied notation
    q = '{"f"};
    q = {q, "f1"};  // push_front
    q = {q, "f2"};  // push_front
    q = {"b1", q};  // push_back
    q = {"b2", q};  // push_back
    `checkp(q, "'{\"b2\", \"b1\", \"f\", \"f1\", \"f2\"}");

    q = {q[0], q[2:$]};  // delete element 1
    `checkp(q, "'{\"b2\", \"f\", \"f1\", \"f2\"}");

    q = {"a", "b"};
    q = {q, q};
    `checkp(q, "'{\"a\", \"b\", \"a\", \"b\"}");

    begin
      static string ai[$] = '{"Foo", "Bar"};
      q = ai;  // Copy
      i = q.size();
      `checkh(i, 2);
      v = q.pop_front();
      `checks(v, "Foo");
      v = q.pop_front();
      `checks(v, "Bar");
      q = '{"BB", "CC"};  // Note '{} not {}
      v = q.pop_front();
      `checks(v, "BB");
      v = q.pop_front();
      `checks(v, "CC");
      q = {"BB", "CC"};  // Note {} not '{}
      v = q.pop_front();
      `checks(v, "BB");
      v = q.pop_front();
      `checks(v, "CC");
    end

    begin
      qi.push_back(0);
      qi.push_back(1);
      qi.push_back(2);
      qi.push_back(3);
      qi.push_back(4);
      qi.push_back(5);

      // Assignment to unsized queue from sized queue
      ri = qi[2 : 4];
      `checkh(ri.size, 3);
      ri = qi[4 : 2];
      `checkh(ri.size, 0);
      ri = qi[2 : 2];
      `checkh(ri.size, 1);
      ri = qi[-2 : 2];  // 2 - 0 + 1 = 3
      `checkh(ri.size, 3);
      ri = qi[2 : 10];  // 5 - 2 + 1 = 4
      `checkh(ri.size, 4);

      // Assignment from unsized to sized
      ri = '{1, 2, 3, 4, 5, 6, 7, 8, 9};
      qi = ri;
      `checkh(qi.size, 5);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
