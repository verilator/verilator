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

module t;
  let LOCK = 1;
  let UNLOCK = 2;
  let ON = 3;
  let OFF = 4;
  let PASS_ON = 6;
  let PASS_OFF = 7;
  let FAIL_ON = 8;
  let FAIL_OFF = 9;

  let SIMPLE_IMMEDIATE = 2;
  let ASSERT = 1;

  int pass_count = 0;
  int fail_count = 0;
  int ctl_type = 0;

  task automatic run_pass();
    assert (1) begin
      pass_count++;
    end else
      `stop;
  endtask

  task automatic run_fail();
    assert (0)
      `stop;
    else begin
      fail_count++;
    end
  endtask

  initial begin
    $assertcontrol(ON, 255, 7);
    $assertcontrol(PASS_ON, 255, 7);
    $assertcontrol(FAIL_ON, 255, 7);

    run_pass();
    `checkd(pass_count, 1);

    // Lock preserves the enabled checking state against OFF.
    $assertcontrol(LOCK, SIMPLE_IMMEDIATE, ASSERT);
    ctl_type = OFF;
    $assertcontrol(ctl_type, SIMPLE_IMMEDIATE, ASSERT);
    run_pass();
    `checkd(pass_count, 2);

    $assertcontrol(UNLOCK, SIMPLE_IMMEDIATE, ASSERT);
    $assertcontrol(OFF, SIMPLE_IMMEDIATE, ASSERT);
    run_pass();
    `checkd(pass_count, 2);

    // Lock preserves the disabled checking state against ON.
    $assertcontrol(LOCK, SIMPLE_IMMEDIATE, ASSERT);
    $assertcontrol(ON, SIMPLE_IMMEDIATE, ASSERT);
    run_pass();
    `checkd(pass_count, 2);

    $assertcontrol(UNLOCK, SIMPLE_IMMEDIATE, ASSERT);
    $assertcontrol(ON, SIMPLE_IMMEDIATE, ASSERT);
    run_pass();
    `checkd(pass_count, 3);

    // Lock also preserves pass-action state.
    $assertcontrol(LOCK, SIMPLE_IMMEDIATE, ASSERT);
    $assertcontrol(PASS_OFF, SIMPLE_IMMEDIATE, ASSERT);
    run_pass();
    `checkd(pass_count, 4);

    $assertcontrol(UNLOCK, SIMPLE_IMMEDIATE, ASSERT);
    $assertcontrol(PASS_OFF, SIMPLE_IMMEDIATE, ASSERT);
    run_pass();
    `checkd(pass_count, 4);

    $assertcontrol(PASS_ON, SIMPLE_IMMEDIATE, ASSERT);

    run_fail();
    `checkd(fail_count, 1);

    // Lock also preserves fail-action state.
    $assertcontrol(LOCK, SIMPLE_IMMEDIATE, ASSERT);
    $assertcontrol(FAIL_OFF, SIMPLE_IMMEDIATE, ASSERT);
    run_fail();
    `checkd(fail_count, 2);

    $assertcontrol(UNLOCK, SIMPLE_IMMEDIATE, ASSERT);
    $assertcontrol(FAIL_OFF, SIMPLE_IMMEDIATE, ASSERT);
    run_fail();
    `checkd(fail_count, 2);

    $assertcontrol(FAIL_ON, SIMPLE_IMMEDIATE, ASSERT);
    run_fail();
    `checkd(fail_count, 3);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
