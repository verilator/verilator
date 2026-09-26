// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  localparam int N = 96;

  wire [N-1:0] sampled;

  // One Observed process per clock, and combinational logic sensitive to all of
  // them, so its trigger test spans a whole word and part of the next
  for (genvar i = 0; i < N; ++i) begin : g
    logic clk = 0;
    logic tog = 0;
    always #(2 + i) clk = ~clk;
    always @(posedge clk) tog <= ~tog;
    clocking cb @(posedge clk);
      input #0 tog;
    endclocking
    assign sampled[i] = cb.tog;
  end

  wire [7:0] ones = $countones(sampled);
  wire parity = ^sampled;

  initial begin
    #700;
    `checkh(sampled, 96'h00000fffc00fe0f8e36dbd87);
    `checkd(ones, 46);
    `checkd(parity, 0);  // zero-ok
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
