// DESCRIPTION: Verilator: force/release and assign/deassign in combinational logic
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off ALWCOMBORDER */
/* verilator lint_off LATCH */
/* verilator lint_off MULTIDRIVEN */
/* verilator lint_off UNDRIVEN */
/* verilator lint_off UNUSEDSIGNAL */
/* verilator lint_off COMBDLY */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */

module t (
    input  logic src,
    output logic assign_out,
    output logic comb_out,
    output logic latch_out
);
  logic assign_sig;
  logic comb_sig;
  logic latch_sig;

  reg a;
  reg q, d;
  event foo;
  real rl;
  int ar [];
  int start = 0;
  int stop = 1;
  int step = 1;
  int done = 0;

  task a_task;
    real trl;
    event tevt;
    reg tvr;
    $display("user task");
  endtask


  always_comb begin : comb_force
    comb_out = comb_sig;
    force comb_sig = src;
    release comb_sig;
  end

  always_latch begin : latch_force
    if (src) latch_out = latch_sig;
    force latch_sig = src;
    release latch_sig;
  end

  always_comb begin : comb_assign
    assign_out = assign_sig;
    assign assign_sig = src;
    deassign assign_sig;
  end

  always_comb begin: blk_name
    event int1, int2;
    real intrl;
    q <= d;
    -> foo;
    rl = 0.0;
    rl <= 1.0;
    ar = new [2];
    for (int idx = start; idx < stop; idx += step) $display("For: %0d", idx);
    for (int idx = 0; done; idx = done + 1) $stop;
    for (int idx = 0; idx; done = done + 1) $stop;
    for (int idx = 0; idx; {done, idx} = done + 1) $stop;
    for (int idx = 0; idx; idx <<= 1) $stop;
    for (int idx = 0; idx; idx = idx << 1) $stop;
    $display("array size: %0d", ar.size());
    ar.delete();
    $display("array size: %0d", ar.size());
    a_task;
    assign a = 1'b0;
    deassign a;
    do $display("do/while");
    while (a);
    force a = 1'b1;
    release a;
    while(a) begin
      $display("while");
      a = 1'b0;
    end
    repeat(2) $display("repeat");
    disable out_name;
    forever begin
      $display("forever");
      disable blk_name; // This one should not generate a warning
    end
  end

  initial begin: out_name
    #2 $stop;
  end

  initial #10 $finish;
endmodule
