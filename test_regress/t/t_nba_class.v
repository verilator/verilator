// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// NBAs may update non-static class properties (IEEE 1800-2023 6.21). The updates are made with
// the other NBAs of the time step, in the order the NBAs executed.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Base;
  int b;
  function void set_b(int v);
    b <= v;
  endfunction
endclass

class Cls #(
    type T = int
) extends Base;
  T x;
  T y;
  function void set_x(T v);
    x <= v;
  endfunction
  task set_y_later(T v);
    y <= #1 v;
  endtask
  task set_y_in_fork(T v);
    fork
      y <= v;
    join_none
  endtask
endclass

module t;
  bit clk;
  int cyc;
  always #5 clk = ~clk;
  always @(posedge clk) cyc <= cyc + 1;

  // Made with the NBA to 'cyc' of the same clock: from a method, also an inherited one, and
  // through a handle, also one read from a dynamic array
  Cls #(int) c = new;
  Cls #(int) cs[];
  initial begin
    cs = new[1];
    cs[0] = new;
  end
  always @(posedge clk) begin
    c.set_x(cyc);
    c.set_b(cyc);
    c.y <= cyc;
    cs[0].x <= cyc;
    // Not before the NBA region
    if (cyc > 0) begin
      `checkd(c.x, cyc - 1);
      `checkd(c.b, cyc - 1);
      `checkd(c.y, cyc - 1);
      `checkd(cs[0].x, cyc - 1);
    end
  end
  initial
    forever begin
      @(cyc);
      `checkd(c.x, cyc - 1);
      `checkd(c.b, cyc - 1);
      `checkd(c.y, cyc - 1);
      `checkd(cs[0].x, cyc - 1);
    end

  // In the order they executed, also from a fork, and with an intra-assignment delay
  Cls #(int) d = new;
  initial begin
    #2;
    d.y <= 1;
    `checkd(d.y, 0);
    d.set_y_in_fork(2);
    `checkd(d.y, 0);
    #1 `checkd(d.y, 2);
    d.set_y_later(3);
    `checkd(d.y, 2);
    // Still not in the active region of the time step it is due
    #1 `checkd(d.y, 2);
    #1 `checkd(d.y, 3);
  end

  initial begin
    #100;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
