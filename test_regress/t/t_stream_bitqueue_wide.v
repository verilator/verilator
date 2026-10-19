// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 0;
  bit q[$];

  always #5 clk = ~clk;

  logic [127:0] vec1;
  logic [127:0] vec2;
  always_ff @(posedge clk) begin
    q = {>>{vec1}};
    vec2 = {>>{q}};
  end

  initial begin
    vec1 = 128'ha0a1aaf03aa1ae4aaa5aa397a2acabaa;
    #100;
    `checkh(vec2, 128'ha0a1aaf03aa1ae4aaa5aa397a2acabaa);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
