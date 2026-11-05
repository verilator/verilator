// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int x;
  int action_count;
  int fail_count;
  int pass_count;
  int fail_arg;
  int pass_arg;
  int late_global;
  int global_value;
  int side_count;
  int multi_count;
  int multi_sum;
  int ref_value;
  int ref_seen;
  int const_ref_seen;
  int static_ref_seen;
  int delayed_count;
  int default_seen;
  int cross_process_count;
  int flush_count;
  int immediate_wait_count;
  logic plain_en;
  logic wait_signal;
  logic wait_immediate_signal;
  int plain_seen;
  string sformat_text;
  event cross_process_flush;
  event resume_event;

  comb_flush u_comb_flush ();
  latch_flush u_latch_flush ();
  delay_flush u_delay_flush ();
  action_args u_action_args ();
  static_assert u_static_assert ();
  cover_flush u_cover_flush ();

  initial begin
    static int a;
    x = 0;
    global_value = 4;
    assert #0 (x != 0) record_pass(x);
    else record_fail(x);
    x = 1;
    `checkd(action_count, 0);
    global_value = 8;
    assert #0 (1) record_pass(side(x));
    `checkd(side_count, 1);
    x = 20;

    for (int i = 0; i < 3; i++) begin
      x = i + 1;
      assert #0 (1) record_multi(x);
    end
    `checkd(multi_count, 0);

    x = 7;
    assert #0 (1) $sformat(sformat_text, "%0d", side(x));
    `checkd(side_count, 2);
    assert #0 (1) $fdisplay(32'h80000001, "%0d", x);
    ref_value = 12;
    assert #0 (1) record_ref(ref_value);
    assert #0 (1) record_const_ref(ref_value);
    assert #0 (1) record_default();
    a = 21;
    assert #0 (1) record_static_ref(a);
    a = 22;
    ref_value = 13;

    #1;
    `checkd(action_count, 2);
    `checkd(fail_count, 1);
    `checkd(fail_arg, 0);
    `checkd(pass_count, 1);
    `checkd(pass_arg, 11);
    `checkd(late_global, 8);
    `checkd(multi_count, 3);
    `checkd(multi_sum, 6);
    `checkd(sformat_text.atoi(), 17);
    `checkd(ref_seen, 13);
    `checkd(const_ref_seen, 13);
    `checkd(static_ref_seen, 22);
    `checkd(default_seen, 9);
    `checkd(flush_count, 0);
    `checkd(immediate_wait_count, 2);

    #1 assert #0 (1) record_delayed();
    `checkd(delayed_count, 0);
    #1;
    `checkd(delayed_count, 1);

    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    #3;
    assert #0 (1) record_cross_process();
    ->cross_process_flush;
    #1;
    `checkd(cross_process_count, 1);
  end

  initial begin
    @cross_process_flush;
  end

  initial begin
    assert #0 (0)
    else record_flush(1);
    @resume_event;
  end

  initial begin
    #0 ->resume_event;
  end

  initial begin
    wait_signal = 0;
    assert #0 (0)
    else record_flush(2);
    wait (wait_signal);
  end

  initial begin
    #0 wait_signal = 1;
  end

  initial begin
    wait_immediate_signal = 1;
    assert #0 (0)
    else record_immediate_wait();
    wait (wait_immediate_signal);
  end

  initial begin
    fork
      #0;
    join_none
    assert #0 (0)
    else record_flush(8);
    wait fork;
  end

  initial begin
    assert #0 (0)
    else record_immediate_wait();
    wait fork;
  end

  initial begin : disable_flush
    assert #0 (0)
    else record_flush(4);
    disable disable_flush;
  end

  initial begin : disable_fork_flush
    fork
      begin
      end
    join
    assert #0 (0)
    else record_flush(16);
    disable disable_fork_flush;
  end

  initial begin : system_action_flush
    assert #0 (1) $system("");
    disable system_action_flush;
  end

  initial begin : stop_action_flush
    assert #0 (1) `stop;
    disable stop_action_flush;
  end

  initial begin : finish_action_flush
    assert #0 (1) $finish;
    disable finish_action_flush;
  end

  initial begin
    wait fork;
  end

  initial begin : plain_disable
    disable plain_disable;
  end

  initial begin : outer_disable
    begin : inner_disable
      disable inner_disable;
    end
  end

  initial begin
    wait (1);
  end

  initial begin
    assert #0 (0)
    else record_flush(0);
    wait (1);
  end

  initial begin
    assert #0 (0)
    else record_flush(0);
    wait (0);
  end

  initial begin
    wait (0);
  end

  always @(plain_en);

  always @* begin
    plain_seen = 0;
    if (plain_en) plain_seen = 1;
  end

  function int side(input int v);
    side_count++;
    return v + 10;
  endfunction

  task record_fail(input int snap);
    action_count++;
    fail_count++;
    fail_arg = snap;
    late_global = global_value;
  endtask

  task record_pass(input int snap);
    action_count++;
    pass_count++;
    pass_arg = snap;
    late_global = global_value;
  endtask

  task record_multi(input int snap);
    multi_count++;
    multi_sum += snap;
  endtask

  task automatic record_ref(ref int snap);
    ref_seen = snap;
  endtask

  task automatic record_const_ref(const ref int snap);
    const_ref_seen = snap;
  endtask

  task automatic record_static_ref(ref int snap);
    static_ref_seen = snap;
  endtask

  task record_default(input int snap = 9);
    default_seen = snap;
  endtask

  task record_cross_process();
    cross_process_count++;
  endtask

  task record_delayed();
    delayed_count++;
  endtask

  task record_flush(input int value);
    flush_count += value;
  endtask

  task record_immediate_wait();
    immediate_wait_count++;
  endtask

  task plain_disable_task();
    begin : task_inner_disable
      disable task_inner_disable;
    end
  endtask

  initial begin
    plain_disable_task();
  end

endmodule

// IEEE 1800-2023 16.4.2: a2 settles in always_comb and reports no failure
module comb_flush;
  logic a;
  logic not_a;
  logic comb_en;
  int comb_reports;

  assign not_a = !a;

  always_comb begin
    if (comb_en) begin
      assert #0 (not_a != a)
      else record_comb();
    end
  end

  initial begin
    a = 0;
    comb_en = 0;
    #2;
    comb_en = 1;
    #1;
    a = 1;
    #1;
    `checkd(comb_reports, 0);
  end

  task record_comb();
    comb_reports++;
  endtask
endmodule

module latch_flush;
  logic a;
  logic not_a;
  logic latch_en;
  logic latch_q;
  int latch_reports;

  assign not_a = !a;

  always_latch begin
    if (latch_en) begin
      latch_q = 1'b1;
      assert #0 (not_a != a)
      else record_latch();
    end
  end

  initial begin
    a = 0;
    latch_en = 0;
    #2;
    latch_en = 1;
    #1;
    a = 1;
    #1;
    `checkd(latch_reports, 0);
  end

  task record_latch();
    latch_reports++;
  endtask
endmodule

// IEEE 1800-2023 16.4.2: a3 always reports, a4 failures are flushed when a or b changes after it
module delay_flush;
  class rpt;
    int successes[2];
    int errors[2];
    task success(int id);
      successes[id]++;
    endtask
    task error(int id, logic a, logic b);
      errors[id]++;
    endtask
  endclass

  logic a = 0;
  logic b = 0;
  rpt rptobj = new;

  always @(a or b) begin : b1
    a3 :
    assert #0 (a == b) rptobj.success(0);
    else rptobj.error(0, a, b);
    #1;
    a4 :
    assert #0 (a == b) rptobj.success(1);
    else rptobj.error(1, a, b);
  end

  initial begin
    #1 a = 1;
    // b1 resumes after a4 fails, flushing it
    #1 b <= 1;
    #2;
    `checkd(rptobj.errors[0], 1);
    `checkd(rptobj.successes[0], 1);
    `checkd(rptobj.errors[1], 0);
    `checkd(rptobj.successes[1], 1);
  end
endmodule

// IEEE 1800-2023 16.4.2: action arguments are evaluated each time a report is queued
module action_args;
  logic my_cond = 1;
  int opcode = 1;
  int a1_reports;
  int a1_type;
  int a2_reports;
  int last_opcode;

  function int error_type(int opcode);
    func_assert :
    assert (opcode < 64)
    else $display("Opcode error.");
    if (opcode < 32) return (0);
    else return (1);
  endfunction

  function void record_a1(int report_type);
    a1_reports++;
    a1_type = report_type;
  endfunction

  function void record_a2(int report_opcode);
    a2_reports++;
    void'(error_type(report_opcode));
  endfunction

  always_comb begin : b1
    a1 :
    assert #0 (my_cond)
    else record_a1(error_type(opcode));
    a2 :
    assert #0 (my_cond)
    else record_a2(opcode);
    last_opcode = opcode;
  end

  initial begin
    #1 my_cond = 0;
    opcode = 64;
    // b1 runs again in the same time step, flushing the reports with opcode 64
    opcode <= 0;
    #1;
    `checkd(a1_reports, 1);
    `checkd(a1_type, 0);
    `checkd(a2_reports, 1);
  end
endmodule

// IEEE 1800-2023 16.4.3: a static deferred assertion behaves as if in an always_comb
module static_defer (
    input logic a,
    input logic b
);
  int reports;
  a1 :
  assert #0 (a == b)
  else record();
  function void record();
    reports++;
  endfunction
endmodule

module static_defer_comb (
    input logic a,
    input logic b
);
  int reports;
  always_comb begin
    a1 :
    assert #0 (a == b)
    else record();
  end
  function void record();
    reports++;
  endfunction
endmodule

module static_assert;
  logic a = 0;
  logic b = 0;

  static_defer u_static (.*);
  static_defer_comb u_comb (.*);

  initial begin
    // The mismatch settles within the time step, so it is flushed
    #1 a = 1;
    b <= 1;
    #1 a = 0;
    #1;
    `checkd(u_static.reports, 1);
    `checkd(u_comb.reports, 1);
  end
endmodule

// IEEE 1800-2023 16.4.2: c2 is not covered by a glitch that b1 flushes
module cover_flush;
  logic a = 0;
  logic b = 0;
  int c2_hits;

  always_comb begin : b1
    c1 : cover (b != a);
    c2 : cover #0 (b != a) record_c2();
  end

  initial begin
    // a and b settle to the same value
    #1 a = 1;
    b <= 1;
    #1;
    `checkd(c2_hits, 0);
    // a and b differ for one time step
    a = 0;
    #1 b = 0;
    `checkd(c2_hits, 1);
  end

  function void record_c2();
    c2_hits++;
  endfunction
endmodule
