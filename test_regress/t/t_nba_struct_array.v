
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t(clk);
  input clk;

  logic [31:0] cyc = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

`define at_posedge_clk_on_cycle(n) always @(posedge clk) if (cyc == n)

  struct {
    int foo;
    int bar;
  } arr [2];

  initial begin
    arr[0].foo = 0;
    arr[0].bar = 100;
    arr[1].foo = 0;
    arr[1].bar = 100;
  end

  `at_posedge_clk_on_cycle(0) begin
    for (int i = 0; i < 2; ++i) begin
      `checkh(arr[i].foo, 0);
      `checkh(arr[i].bar, 100);
    end
  end
  `at_posedge_clk_on_cycle(1) begin
    for (int i = 0; i < 2; ++i) begin
      `checkh(arr[i].foo, 0);
      `checkh(arr[i].bar, 100);
    end
    arr[0].foo <=  0;
    arr[0].bar <= -0;
    arr[1].foo <=  1;
    arr[1].bar <= -1;
    for (int i = 0; i < 2; ++i) begin
      `checkh(arr[i].foo, 0);
      `checkh(arr[i].bar, 100);
    end
  end
  `at_posedge_clk_on_cycle(2) begin
    for (int i = 0; i < 2; ++i) begin
      `checkh(arr[i].foo,  i);
      `checkh(arr[i].bar, -i);
    end
    arr[0].foo <= ~0;
    arr[0].bar <=  0;
    arr[1].foo <= ~1;
    arr[1].bar <=  1;
    for (int i = 0; i < 2; ++i) begin
      `checkh(arr[i].foo,  i);
      `checkh(arr[i].bar, -i);
    end
  end
  `at_posedge_clk_on_cycle(3) begin
    for (int i = 0; i < 2; ++i) begin
      `checkh(arr[i].foo, ~i);
      `checkh(arr[i].bar,  i);
    end
    arr[0].foo <= -1;
    arr[0].bar <= -2;
    arr[1].foo <= -1;
    arr[1].bar <= -2;
    for (int i = 0; i < 2; ++i) begin
      `checkh(arr[i].foo, ~i);
      `checkh(arr[i].bar,  i);
    end
  end
  `at_posedge_clk_on_cycle(4) begin
    for (int i = 0; i < 2; ++i) begin
      `checkh(arr[i].foo, -1);
      `checkh(arr[i].bar, -2);
    end
  end


endmodule
