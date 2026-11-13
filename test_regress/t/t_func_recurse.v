// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  function automatic int recurse_self;
    input int i;
    if (i == 0) recurse_self = 0;
    else recurse_self = i + recurse_self(i - 1) * 2;
  endfunction

  initial begin
    `checkd(recurse_self(0), 0);

    `checkd(recurse_self(3), (3 + 2 * (2 + 2 * (1))));
  end

  // Recursive call from clocked logic, scheduled by the multithreaded scheduler
  int cyc = 0;
  int result;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    result <= recurse_self(cyc);

    if (cyc == 3) `checkd(result, 4);

    if (cyc == 4) `checkd(result, 11);

    // Complete after the submodule's cycle-4 check, regardless of process order.
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  sub u_sub (.clk);

endmodule

// Hierarchical block (with --hierarchical) holding a recursive call
module sub (
    input clk
);  /*verilator hier_block*/

  function automatic int fact(int n);
    if (n <= 1) return 1;
    return n * fact(n - 1);
  endfunction

  int cyc = 0;
  int result;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    result <= fact(cyc);

    if (cyc == 4) `checkd(result, 6);
  end

endmodule
