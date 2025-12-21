// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub (
    input clk,
    input b
);  /*verilator hier_block*/
  reg tmp_clk;
  assign tmp_clk = clk;

  always @(posedge tmp_clk) begin
    $display("[%0t] triggered by clk", $time);
  end

  int count = 0;
  always @(b) begin
`ifdef TEST_VERBOSE
    $display("[%0t] triggered by b", $time);
`endif
    ++count;
  end
  final `checkd(count, 2);
endmodule

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;
  logic b = 1;

  sub sub (.*);

  int cyc = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc >= 2) begin
      $finish;
    end
  end
endmodule
