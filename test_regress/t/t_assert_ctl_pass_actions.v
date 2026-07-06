// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin \
  $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", \
         `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); \
  `stop; \
end while (0)
// verilog_format: on

`ifdef VERILATOR
// The '$c(1)' is there to prevent inlining of the signal by V3Gate.
`define IMPURE_ONE ($c(1))
`else
// Use standard $random. The chance of getting 2 consecutive zeroes is negligible.
`define IMPURE_ONE (|($random | $random))
`endif

interface AssertCtlIface;
  bit run_initial = 0;
  bit initial_done = 0;
  int fails = 0;

  function void clear();
    fails = 0;
  endfunction
  function void assert_off();
    $assertcontrol(4, 2, 1);
  endfunction
  function void assert_on();
    $assertcontrol(3, 2, 1);
  endfunction
  function void fail_check();
    assert (0) `stop;
    else fails++;
  endfunction
  function void run_checks();
    assert_off();
    fail_check();
    assert_on();
    fail_check();
  endfunction

  initial begin
    wait (run_initial);
    run_checks();
    initial_done = 1;
  end
endinterface

module t;
  bit clk = 0;
  int imm_passes = 0;
  int imm_fails = 0;
  int vacuous_passes = 0;
  int nonvacuous_passes = 0;
  int concurrent_fails = 0;
  int class_fails = 0;

  class AssertCtlClass;
    function void assert_off();
      $assertcontrol(4, 2, 1);
    endfunction
    function void assert_on();
      $assertcontrol(3, 2, 1);
    endfunction
    function void fail_check();
      assert (0) `stop;
      else class_fails++;
    endfunction
  endclass

  AssertCtlClass assert_ctl_class;
  AssertCtlIface assert_ctl_iface ();
  virtual AssertCtlIface v_assert_ctl_iface = assert_ctl_iface;

  always #5 clk = !clk;

  default clocking @(posedge clk);
  endclocking

  assert property (@(posedge clk) 1'b0 |-> ##1 1'b1) begin
    vacuous_passes++;
  end
  else `stop;

  assert property (@(posedge clk) 1'b1 |-> ##1 1'b1) begin
    nonvacuous_passes++;
  end
  else `stop;

  assert property (@(posedge clk) 1'b1 |-> ##1 1'b0) begin
  end
  else concurrent_fails++;

  task automatic tick_and_check(input int exp_vacuous, input int exp_nonvacuous,
                                input int exp_concurrent_fails);
    @(posedge clk);
    #2;
    `checkd(vacuous_passes, exp_vacuous);
    `checkd(nonvacuous_passes, exp_nonvacuous);
    `checkd(concurrent_fails, exp_concurrent_fails);
  endtask

  initial begin
    assert_ctl_class = new;

    $assertcontrol(4, 16, 1);
    $assertcontrol(5, 16, 1);
    $assertcontrol(3 * `IMPURE_ONE, 2 * `IMPURE_ONE);

    $assertcontrol(3, 255, 7);
    $assertcontrol(6, 255, 7);
    $assertcontrol(8, 255, 7);

    assert (1) imm_passes++;
    else `stop;
    `checkd(imm_passes, 1);

    $assertcontrol(1, 2, 1);
    $assertcontrol(4, 2, 1);
    assert (1) imm_passes++;
    else `stop;
    `checkd(imm_passes, 2);

    $assertcontrol(2, 2, 1);
    $assertcontrol(4, 2, 1);
    assert (1) imm_passes++;
    else `stop;
    `checkd(imm_passes, 2);

    $assertcontrol(3, 2, 1);

    $assertcontrol(1, 2, 1);
    $assertcontrol(7, 2, 1);
    assert (1) imm_passes++;
    else `stop;
    `checkd(imm_passes, 3);

    $assertcontrol(2, 2, 1);
    $assertcontrol(7, 2, 1);
    assert (1) imm_passes++;
    else `stop;
    `checkd(imm_passes, 3);

    $assertcontrol(10, 2, 1);
    assert (1) imm_passes++;
    else `stop;
    `checkd(imm_passes, 4);

    $assertcontrol(11, 2, 1);
    assert (1) imm_passes++;
    else `stop;
    `checkd(imm_passes, 5);

    $assertcontrol(6, 2, 1);

    assert (0) `stop;
    else imm_fails++;
    `checkd(imm_fails, 1);

    $assertcontrol(1, 2, 1);
    $assertcontrol(9, 2, 1);
    assert (0) `stop;
    else imm_fails++;
    `checkd(imm_fails, 2);

    $assertcontrol(2, 2, 1);
    $assertcontrol(9, 2, 1);
    assert (0) `stop;
    else imm_fails++;
    `checkd(imm_fails, 2);

    $assertcontrol(8, 2, 1);
    assert (0) `stop;
    else imm_fails++;
    `checkd(imm_fails, 3);

    assert_ctl_class.assert_off();
    assert_ctl_class.fail_check();
    `checkd(class_fails, 0);

    assert_ctl_class.assert_on();
    assert_ctl_class.fail_check();
    `checkd(class_fails, 1);

    assert_ctl_iface.run_initial = 1;
    wait (assert_ctl_iface.initial_done);
    `checkd(assert_ctl_iface.fails, 1);

    assert_ctl_iface.clear();
    assert_ctl_iface.run_checks();
    `checkd(assert_ctl_iface.fails, 1);

    assert_ctl_iface.clear();
    v_assert_ctl_iface.run_checks();
    `checkd(assert_ctl_iface.fails, 1);

    $assertcontrol(9, 1, 1);

    tick_and_check(1, 0, 0);
    tick_and_check(2, 1, 0);

    $assertcontrol(11, 1, 1);
    tick_and_check(2, 2, 0);

    $assertcontrol(7, 1, 1);
    tick_and_check(2, 2, 0);

    $assertcontrol(10, 1, 1);
    tick_and_check(2, 3, 0);

    $assertcontrol(6, 1, 1);
    tick_and_check(3, 4, 0);

    $assertcontrol(8, 1, 1);
    tick_and_check(4, 5, 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
