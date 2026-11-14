// DESCRIPTION: Verilator: wait trigger evaluation through null references
// SPDX-FileCopyrightText: 2026 Xia Chao

// SPDX-License-Identifier: CC0-1.0

// wait triggers are evaluated at time 0, before their process starts; a null
// class or fork dynamic-scope member access must not fault in that early eval.

`define stop $stop

module t;
  class Cls;
    int x = 0;
  endclass

  int checks = 0;

  task automatic finish_if_done();
    if (checks == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  endtask

  Cls c;

  // Wait on a class member before the handle is assigned.
  initial begin
    wait (c != null);
    wait (c.x == 1);
    if (c.x !== 1) `stop;
    checks++;
    finish_if_done();
  end

  initial begin
    c = new;
    c.x = 1;
  end

  // Two independent handles are null in the same trigger at time 0.
  Cls d;

  initial begin
    wait (c != null);
    wait (d != null);
    wait (c.x == d.x);
    checks++;
    finish_if_done();
  end

  initial begin
    d = new;
    d.x = 1;
  end

  int flag = 0;
  bit dyn_done = 0;

  // Wait on an automatic task local inside a deferred fork branch.
  task automatic dyn_wait();
    automatic int id = 1;
    fork
      begin
        wait (flag == id);
        dyn_done = 1;
      end
    join_none
    wait fork;
  endtask

  initial begin
    flag = 1;
    dyn_wait();
    if (!dyn_done) `stop;
    checks++;
    finish_if_done();
  end

  bit enabled = 0;

  // The fork is never entered, but its wait trigger is still evaluated.
  task automatic unreached();
    if (!enabled) return;
    fork
      wait (c.x == 2);
    join
  endtask

  initial begin
    unreached();
    checks++;
    finish_if_done();
  end
endmodule
