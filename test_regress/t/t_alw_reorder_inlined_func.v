// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: $time=%0t got='h%x exp='h%x\n", `__FILE__,`__LINE__, $time, (got), (exp)); `stop; end while(0)
// verilog_format: on

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;

  // Constant 1 set in initial block, but not known at compile time
  logic enable = 1'b0;

  int array[32];

  function automatic int get(logic en, logic [4:0] idx);
    if (en) begin  // Always taken, but need the 'if' to show bug
      int tmp;
      idx = ~idx;
      tmp = array[~idx];
      return tmp;
    end
    else begin
      return 0;
    end
  endfunction

  int q;
  always @(posedge clk) begin
    // Function inlined on RHS or NBA used to have its body reordered as if
    // assignments in the body were NBAs themselves.
    q <= cyc == 0 ? 0 : get(enable, 5'(cyc));
  end

  initial begin
    enable = 1'b1;
    for (int n = 0; n < 32; ++n) begin
      array[n] = 100 + n;
    end

    repeat (100) begin
      @(posedge clk);
      #1;
      $display("$08t %3d %3d", $time, cyc - 1, q);
      `check(q, cyc == 1 ? 0 : 100 + (cyc - 1) % 32);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
