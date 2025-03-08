// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef struct {
   string name1;
   string name2;
} names_t;

class uvm_queue;
   names_t m_queue[$];

   virtual function void push_back(names_t item);
      m_queue.push_back(item);
   endfunction
endclass

module t(/*AUTOARG*/);

   uvm_queue q;

   initial begin
      q = new;
      // From uvm_queue#(uvm_acs_name_struct) __local_field_names__;
      q.push_back('{"n1", "n2"});
      q.push_back('{"m1", "m2"});
      q.m_queue.push_back('{"o1", "o2"});
      $display("%p", q);
      `checks(q.m_queue[0].name1, "n1");
      `checks(q.m_queue[0].name2, "n2");
      `checks(q.m_queue[1].name1, "m1");
      `checks(q.m_queue[1].name2, "m2");
      `checks(q.m_queue[2].name1, "o1");
      `checks(q.m_queue[2].name2, "o2");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
