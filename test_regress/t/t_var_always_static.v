// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk;
  int out;
  int out2;
  int expected;

  always_ff @(posedge clk) begin
    automatic int proc_auto = 0;
    static int proc_static = 8;
    proc_auto = proc_auto + 1;
    proc_static = proc_static + proc_auto;
    out <= proc_static;
    out2 <= func_out2();
  end

  function int func_out2();
    automatic int func_auto = 0;
    static int func_static = 8;
    func_auto = func_auto + 1;
    func_static = func_static + func_auto;
    return func_static;
  endfunction

  initial begin
    `checkd(A.i1, 1);
    `checkd(A.i2, 2);
    `checkd(A.i3, 3);
    `checkd(A.t, 0);
    #1;
    begin : A
      static int i1 = 1;
      static int i2 = i1 + 1;
      static int i3 = i2 + 1;
      static time t = $time;  // Initializes at 0, not current time (all simulators agree)
      `checkd(i1, 1);
      `checkd(i2, 2);
      `checkd(i3, 3);
      `checkd(t, 0);
    end
  end

  initial begin
    clk = 0;

    for (int cycle = 0; cycle < 20; ++cycle) begin
      clk = 0;
      #5;
      clk = 1;
      #4;
      // Print outputs after each positive clock edge
      expected = (cycle == 0) ? 9 : (9 + cycle);
      $display("[%0t] got=%0d %0d | exp=%0d", $time, out, out2, expected);
      `checkd(out, expected);
      `checkd(out2, expected);
      #1;
    end

    $finish;
  end

endmodule
