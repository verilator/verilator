// DESCRIPTION: Verilator: Synchronous drive of a concatenation of clockvars
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit clk;
  bit a;
  bit b;
  string a_log;
  string b_log;

  always #5 clk = ~clk;

  clocking pe @(posedge clk);
    output a, b;
  endclocking

  always @(a) if ($time != 0) a_log = {a_log, $sformatf("%0d@%0d ", a, $time)};
  always @(b) if ($time != 0) b_log = {b_log, $sformatf("%0d@%0d ", b, $time)};

  // IEEE 1800-2023 14.16 does not allow a concatenation as the target of a synchronous drive,
  // but other simulators accept it and drive each clockvar, also with the value last driven
  initial begin
    @(pe);
    {pe.a, pe.b} <= 2'b11;
    #2;
    a = 0;
    b = 0;
    @(pe);
    {pe.a, pe.b} <= 2'b11;
    #2;
    a = 0;
    b = 0;
    // '##0' has no effect, so is accepted, unlike other cycle delays (see t_clocking_bad4)
    @(pe);
    {pe.a, pe.b} <= ##0 2'b11;
  end

  initial begin
    #40;
    `checks(a_log, "1@5 0@7 1@15 0@17 1@25 ")
    `checks(b_log, "1@5 0@7 1@15 0@17 1@25 ")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
