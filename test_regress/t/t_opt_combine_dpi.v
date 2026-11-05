// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  import "DPI-C" function int dpii_count();

  sub u1 ();
  sub u2 ();

  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  logic [1:0] div = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    div <= div + 1;
    if (cyc == 16) begin
      `checkd(dpii_count(), 16);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Processes on different clocks, so each is in its own function. The two calling
  // 'u2' are combined, then the DPI wrappers of 'u1' and 'u2' in 'sub' are combined.
  always @(posedge div[0]) u1.dpii_f();
  always @(posedge div[1]) u2.dpii_f();
  always @(negedge div[1]) u2.dpii_f();

endmodule

module sub;
  /*verilator no_inline_module*/
  import "DPI-C" function void dpii_f();
endmodule
