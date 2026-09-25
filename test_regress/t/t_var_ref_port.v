// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A ref port is another name for the variable it is connected to, so a write at
// either end must be seen at the other.
module sub (
    input bit clk,
    input int cyc,
    ref int y
);
  always @(posedge clk) begin
    if (cyc == 1) y <= 100;
    else if (cyc == 2) `checkd(y, 100)
    else if (cyc == 4) `checkd(y, 200)  // Written by 't'
  end
endmodule

// A ref port read from a task of the instance.
module subtask (
    ref int z
);
  task static check(int expv);
    `checkd(z, expv)
  endtask
endmodule

module t;

  bit clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  // Driven both here and in 'sub' via the ref port - that being the point of this test
  // verilator lint_off MULTIDRIVEN
  int x;
  // verilator lint_on MULTIDRIVEN
  int w = 15;

  sub s (clk, cyc, x);
  subtask st (.z(w));

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) begin
      `checkd(x, 100)  // Written by 's'
    end else if (cyc == 3) begin
      x <= 200;
    end else if (cyc == 4) begin
      `checkd(x, 200)
      st.check(15);
      w = 16;
      st.check(16);
    end else if (cyc == 5) begin
      `checkd(w, 16)
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
