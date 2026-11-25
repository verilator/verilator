// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) \
  do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0)
// verilog_format: on

module t;
  bit clk;
  always #1 clk = ~clk;

  // An always process killed by another process
  process always_victim;
  bit always_killed;

  initial begin
    wait (always_victim);
    always_victim.kill();
    always_victim.await();
    always_killed = 1'b1;
  end

  always @(posedge clk) begin
    if (!always_victim) begin
      always_victim = process::self();
    end
    else begin
      $stop;
    end
  end

  // Processes killing themselves, directly or in called functions
  bit direct_after;
  bit nested_after;
  int nested_value = -1;
  bit expression_after;
  int expression_value = -1;
  bit virtual_deep_after;
  bit virtual_caller_after;
  bit external_after;
  bit inactive_after;
  process direct_process;
  process nested_process;
  process expression_process;
  process virtual_process;
  process inactive_process;
  process victim;

  class killer;
    function automatic int kill_deep(process p);
      if (1) begin
        repeat (1) begin
          p.kill();
        end
      end
      return 42;
    endfunction

    function automatic int call_kill_deep(process p);
      return kill_deep(p);
    endfunction
  endclass

  class base_killer;
    virtual function automatic void kill_virtual(process p);
    endfunction
  endclass

  class derived_killer extends base_killer;
    function automatic void kill_virtual(process p);
      p.kill();
      virtual_deep_after = 1'b1;
    endfunction
  endclass

  initial begin
    automatic killer k = new();
    automatic derived_killer derived = new();
    automatic base_killer polymorphic = derived;
    automatic int external_value;
    fork
      begin
        automatic process p = process::self();
        direct_process = p;
        #1;
        p.kill();
        direct_after = 1'b1;
      end
      begin
        automatic process p = process::self();
        nested_process = p;
        #2;
        nested_value = k.call_kill_deep(p);
        nested_after = 1'b1;
      end
      begin
        expression_process = process::self();
        #2;
        expression_value = 1 + k.call_kill_deep(expression_process);
        expression_after = 1'b1;
      end
      begin
        automatic process p = process::self();
        virtual_process = p;
        #3;
        polymorphic.kill_virtual(p);
        virtual_caller_after = 1'b1;
      end
      begin
        automatic process p = process::self();
        inactive_process = p;
        #0;
        p.kill();
        inactive_after = 1'b1;
      end
    join_none

    fork
      begin
        victim = process::self();
        #20;
      end
    join_none
    wait (victim != null);
    #3;
    external_value = k.kill_deep(victim);
    `checkd(external_value, 42);
    external_value = 1 + k.call_kill_deep(victim);
    `checkd(external_value, 43);
    external_after = 1'b1;
    #10;

    `checkd(direct_after, 1'b0);
    `checkd(nested_after, 1'b0);
    `checkd(nested_value, -1);
    `checkd(expression_after, 1'b0);
    `checkd(expression_value, -1);
    `checkd(virtual_deep_after, 1'b0);
    `checkd(virtual_caller_after, 1'b0);
    `checkd(inactive_after, 1'b0);
    `checkd(external_after, 1'b1);
    `checkd(direct_process.status(), process::KILLED);
    `checkd(nested_process.status(), process::KILLED);
    `checkd(expression_process.status(), process::KILLED);
    `checkd(virtual_process.status(), process::KILLED);
    `checkd(inactive_process.status(), process::KILLED);
    `checkd(victim.status(), process::KILLED);
    `checkd(always_killed, 1'b1);
    $finish;
  end

  // A process still waiting at $finish, killed in a final block
  process final_victim;
  int final_completed;

  initial begin
    fork
      begin
        final_victim = process::self();
        #100;
        ++final_completed;
      end
    join_none
  end

  final begin
    `checkd(final_victim != null, 1'b1);
    `checkd(final_victim.status(), process::WAITING);
    final_victim.kill();
    `checkd(final_victim.status(), process::KILLED);
    `checkd(final_completed, 0);
    $write("*-* All Finished *-*\n");
  end
endmodule
