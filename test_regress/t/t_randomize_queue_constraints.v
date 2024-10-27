// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
   if (!bit'(cl.randomize())) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(9) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class Foo;
  rand int m_intQueue[$];
  rand int m_idx;

  function new;
    m_intQueue = '{10{0}};
  endfunction

  constraint int_queue_c {
    m_idx inside {[0:9]};
    m_intQueue[m_idx] == m_idx + 1;
    foreach (m_intQueue[i]) {
      m_intQueue[i] inside {[0:127]};
    }
  }
endclass

module t_randomize_queue_constraints;
  initial begin
    Foo foo = new;

    `check_rand(foo, foo.m_idx, foo.m_idx inside {[0:9]} && foo.m_intQueue[foo.m_idx] == foo.m_idx + 1);
    $display("Queue: %p", foo.m_intQueue);
    `check_rand(foo, foo.m_intQueue[3], foo.m_intQueue[5] inside {[0:127]});
    $display("Queue: %p", foo.m_intQueue);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
