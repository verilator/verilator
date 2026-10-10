
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  logic clk = 0;
  always #5 clk = ~clk;

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

  // An NBA to a member of an array element, after waiting or in a fork, updates the element
  // that was selected when the NBA ran, even if the index changes afterwards
  struct {
    int foo;
    int bar;
  } warr [2];
  int widx = 0;
  int fidx = 1;
  initial begin
    @(posedge clk);
    warr[widx].foo <= 1;
    widx = 1;
  end
  initial
  fork
    begin
      warr[fidx].bar <= 2;
      fidx = 0;
    end
  join_none
  // Also through several levels of arrays and structs
  typedef struct {int q[3];} inner_t;
  typedef struct {inner_t z;} elem_t;
  typedef struct {elem_t a[2];} outer_t;
  outer_t nest;
  int nidx = 1;
  int qidx = 2;
  initial begin
    @(posedge clk);
    nest.a[nidx].z.q[qidx] <= 5;
    nidx = 0;
    qidx = 0;
  end
  `at_posedge_clk_on_cycle(5) begin
    `checkh(warr[0].foo, 1);
    `checkh(warr[1].foo, 0);
    `checkh(warr[0].bar, 0);
    `checkh(warr[1].bar, 2);
    `checkh(nest.a[1].z.q[2], 5);
    `checkh(nest.a[0].z.q[2], 0);
    `checkh(nest.a[0].z.q[0], 0);
  end


endmodule
