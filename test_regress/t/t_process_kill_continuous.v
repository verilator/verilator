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
  process worker[3];
  int ticks[3];
  bit trig_assign, trig_comb, trig_star, trig_self;
  bit res_assign, res_comb, res_star;

  function automatic bit kill_worker(int i, bit cond);
    if (cond) worker[i].kill();
    return cond;
  endfunction

  // kill() called from each kind of combinational logic
  assign res_assign = kill_worker(0, trig_assign);
  always_comb res_comb = kill_worker(1, trig_comb);
  always @* res_star = kill_worker(2, trig_star);

  class self_killer;
    int calls;

    task run();
      automatic process current = process::self();
      ++calls;
      current.kill();
    endtask
  endclass

  self_killer killer = new;
  always @* if (trig_self) killer.run();

  initial begin
    for (int i = 0; i < 3; ++i) begin
      fork
        automatic int j = i;
        begin
          worker[j] = process::self();
          forever #2 ticks[j]++;  // Ticks at t=2, t=4, ...
        end
      join_none
    end

    #5;
    trig_assign = 1'b1;
    trig_comb = 1'b1;
    trig_star = 1'b1;
    trig_self = 1'b1;
    #1;
    `checkd(res_assign, 1'b1);
    `checkd(res_comb, 1'b1);
    `checkd(res_star, 1'b1);
    `checkd(killer.calls, 1);
    for (int i = 0; i < 3; ++i) `checkd(worker[i].status(), process::KILLED);

    {trig_assign, trig_comb, trig_star, trig_self} = 4'b0000;
    #1;
    `checkd({res_assign, res_comb, res_star}, 3'b000);
    trig_self = 1'b1;
    #1;
    `checkd(killer.calls, 1);
    #3;
    for (int i = 0; i < 3; ++i) `checkd(ticks[i], 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
