// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Disabling a named fork in one module instance must not terminate branches of
// the same syntactic fork in another module instance.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class QueueHolder;
  typedef int int_queue_t[$];
  int member_queue[$];

  function automatic int_queue_t temporary_queue();
    int_queue_t result;
    return result;
  endfunction

  task run_temporary();
    fork
      temporary_queue().push_back(2);
    join
  endtask
endclass

module child (
    input bit do_disable,
    output bit survived_a,
    output bit survived_b,
    output bit done
);

  initial begin
    fork : fork_blk
      begin
        if (do_disable) begin
          #1;
          disable fork_blk;
          $stop;
        end
        else begin
          #6;
          survived_a = 1'b1;
        end
      end
      begin
        if (do_disable) begin
          #5 $stop;
        end
        else begin
          #6;
          survived_b = 1'b1;
        end
      end
    join
    done = 1'b1;
  end
endmodule

module t;

  bit do_disable0 = 1'b1;
  bit do_disable1 = 1'b0;
  bit survived_a0;
  bit survived_b0;
  bit done0;
  bit survived_a1;
  bit survived_b1;
  bit done1;
  QueueHolder holder;

  child child0 (
      .do_disable(do_disable0),
      .survived_a(survived_a0),
      .survived_b(survived_b0),
      .done(done0)
  );

  child child1 (
      .do_disable(do_disable1),
      .survived_a(survived_a1),
      .survived_b(survived_b1),
      .done(done1)
  );

  initial begin
    // Cover queue receivers that are class members and temporary expressions.
    holder = new;
    fork
      holder.member_queue.push_back(1);
      holder.run_temporary();
    join
    #7;
    `checkd(holder.member_queue.size(), 1);
    `checkd(done0, 1'b1);
    `checkd(done1, 1'b1);
    `checkd(survived_a1, 1'b1);
    `checkd(survived_b1, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
