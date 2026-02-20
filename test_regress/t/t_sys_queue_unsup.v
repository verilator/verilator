// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Based on iverilog/ivtest/ivltests/queue.v

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module top;
  reg pass;
  integer res, status, job, value;

  initial begin
    pass = 1'b1;
    $q_initialize(1, 1, 3, status);
    `checkd(status, 0);

    $q_initialize(2, 2, 2, status);
    `checkd(status, 0);

    $q_initialize(3, 0, 10, status);
    `checkd(status, 4);

    $q_initialize(3, 3, 10, status);
    `checkd(status, 4);

    $q_initialize(3, 1, 0, status);
    `checkd(status, 5);

    $q_initialize(3, 1, -1, status);
    `checkd(status, 5);

    $q_initialize(1, 2, 20, status);
    `checkd(status, 6);

    $q_add(3, 0, 0, status);
    `checkd(status, 2);

    $q_remove(3, job, value, status);
    `checkd(status, 2);

    res = $q_full(3, status);
    `checkd(status, 2);

    $q_exam(3, 1, value, status);
    `checkd(status, 2);

    $q_add(2, 1, 1, status);
    `checkd(status, 0);

    res = $q_full(2, status);
    `checkd(status, 0);
    `checkd(res, 0);

    $q_add(2, 1, 2, status);
    `checkd(status, 0);

    res = $q_full(2, status);
    `checkd(status, 0);
    `checkd(res, 1);

    $q_exam(2, 1, value, status);
    `checkd(status, 0);
    `checkd(value, 2);
    $q_exam(2, 3, value, status);
    `checkd(status, 0);
    `checkd(value, 2);
    $q_exam(2, 5, value, status);
    `checkd(status, 0);
    `checkd(value, 0);

    $q_add(2, 1, 3, status);
    `checkd(status, 1);

    $q_remove(2, job, value, status);
    `checkd(status, 0);
    `checkd(job, 1);
    `checkd(value, 2);
    res = $q_full(2, status);
    `checkd(status, 0);
    `checkd(res, 0);

    $q_remove(2, job, value, status);
    `checkd(status, 0);
    `checkd(job, 1);
    `checkd(value, 1);

    res = $q_full(2, status);
    `checkd(status, 0);
    `checkd(res, 0);

    $q_exam(2, 1, value, status);
    `checkd(status, 0);
    `checkd(value, 0);
    $q_exam(2, 3, value, status);
    `checkd(status, 0);
    `checkd(value, 2);
    $q_exam(2, 4, value, status);
    `checkd(status, 0);
    `checkd(value, 0);

    $q_remove(2, job, value, status);
    `checkd(status, 3);


    $q_add(1, 2, 1, status);
    `checkd(status, 0);
    res = $q_full(1, status);
    `checkd(status, 0);
    `checkd(res, 0);
    $q_add(1, 2, 2, status);
    `checkd(status, 0);
    res = $q_full(1, status);
    `checkd(status, 0);
    `checkd(res, 0);
    $q_add(1, 2, 3, status);
    `checkd(status, 0);
    res = $q_full(1, status);
    `checkd(status, 0);
    `checkd(res, 1);
    $q_exam(1, 1, value, status);
    `checkd(status, 0);
    `checkd(value, 3);
    $q_exam(1, 3, value, status);
    `checkd(status, 0);
    `checkd(value, 3);
    $q_exam(1, 5, value, status);
    `checkd(status, 0);
    `checkd(value, 0);

    $q_add(1, 2, 4, status);
    `checkd(status, 1);

    $q_remove(1, job, value, status);
    `checkd(status, 0);
    `checkd(job, 2);
    `checkd(value, 1);

    res = $q_full(1, status);
    `checkd(status, 0);
    `checkd(res, 0);

    $q_remove(1, job, value, status);
    `checkd(status, 0);
    `checkd(job, 2);
    `checkd(value, 2);
    res = $q_full(1, status);
    `checkd(status, 0);
    `checkd(res, 0);

    $q_add(1, 2, 4, status);
    `checkd(status, 0);
    res = $q_full(1, status);
    `checkd(status, 0);
    `checkd(res, 0);

    $q_remove(1, job, value, status);
    `checkd(status, 0);
    `checkd(job, 2);
    `checkd(value, 3);
    res = $q_full(1, status);
    `checkd(status, 0);
    `checkd(res, 0);
    $q_remove(1, job, value, status);
    `checkd(status, 0);
    `checkd(job, 2);
    `checkd(value, 4);
    res = $q_full(1, status);
    `checkd(status, 0);
    `checkd(res, 0);
    $q_exam(1, 1, value, status);
    `checkd(status, 0);
    `checkd(value, 0);
    $q_exam(1, 3, value, status);
    `checkd(status, 0);
    `checkd(value, 3);
    $q_exam(1, 4, value, status);
    `checkd(status, 0);
    `checkd(value, 0);

    $q_remove(1, job, value, status);
    `checkd(status, 3);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
