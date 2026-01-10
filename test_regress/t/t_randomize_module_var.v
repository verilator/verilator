// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0


module t_randomize_module_var;
  int golden_queue[$];

  class Cls;
    rand bit deq;
    constraint valid_enq {
      if (golden_queue.size() == 0) {
        deq == 0;
      }
    }
  endclass

  Cls tr;

  initial begin
    tr = new;

    // Test 1: Empty queue - deq must be 0
    if (tr.randomize() == 0) begin
      $stop;
    end
    if (tr.deq != 0) begin
      $display("Error: Expected deq=0 when queue is empty, got %0d", tr.deq);
      $stop;
    end

    // Test 2: Non-empty queue - deq can be 0 or 1
    golden_queue.push_back(42);
    if (tr.randomize() == 0) begin
      $stop;
    end
    // deq can be 0 or 1, both are valid

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
