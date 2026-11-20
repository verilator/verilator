// DESCRIPTION: Verilator: wait trigger evaluation through null references
/*
 * This file ONLY is placed under the Creative Commons Public Domain.
 * SPDX-FileCopyrightText: 2026 Xia Chao
 * SPDX-License-Identifier: CC0-1.0
 */

// A wait on a null class or fork dynamic-scope member must not fault.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  class Cls;
    int x = 0;
  endclass

  int checks = 0;

  task automatic finish_if_done();
    if (checks == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  endtask

  Cls c;

  // Wait on a class member before the handle is assigned.
  initial begin
    wait (c != null);
    wait (c.x == 1);
    `checkd(c.x, 1);
    checks++;
    finish_if_done();
  end

  initial begin
    c = new;
    c.x = 1;
  end

  // Two independent null handles in one wait.
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

  class Outer;
    Cls inner;
  endclass

  // A wait through a nested null class chain must not fault.
  Outer o;

  initial begin
    wait (o != null);
    wait (o.inner != null);
    wait (o.inner.x == 2);
    checks++;
    finish_if_done();
  end

  initial begin
    o = new;
    o.inner = new;
    o.inner.x = 2;
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
    `checkd(dyn_done, 1);
    checks++;
    finish_if_done();
  end

  bit enabled = 0;

  // A fork that is never entered must not fault.
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
