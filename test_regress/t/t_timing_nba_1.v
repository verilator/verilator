// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
  integer cyc = 0;

  reg [7:0] a;
  reg [127:0] b;

  always #1 begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      a <= 8'hFF;
      a[7] <= 1'b0;
    end
    else if (cyc == 1) begin
`ifdef TEST_VERBOSE
      $write("a = %x\n", a);
`endif
      if (a != 8'h7F) $stop;
    end
    else if (cyc == 2) begin
      b <= 128'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
      b[127] <= 1'b0;
    end
    else if (cyc == 3) begin
`ifdef TEST_VERBOSE
      $write("b = %x\n", b);
`endif
      if (b != 128'h7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) $stop;
    end
    else if (cyc > 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // NBAs to a whole unpacked array update it: after a delay, in a fork, and in a clocked
  // process. An NBA to a single element updates it too.
  logic clk = 0;
  logic [7:0] arr[0:3];
  logic [7:0] arr_fork[0:3];
  logic [7:0] arr_clk[0:3];
  logic [7:0] arr_elem[0:3];
  logic [7:0] arr_src[0:3] = '{8'h11, 8'h22, 8'h33, 8'h44};
  int idx;
  initial #1 arr <= arr_src;
  initial
  fork
    #1 arr_fork <= arr_src;
  join_none
  initial #1 clk = 1;
  always @(posedge clk) begin
    arr_clk <= arr_src;
    arr_elem[1] <= arr_src[1];
  end
  initial begin
    #2;
    foreach (arr_src[i]) begin
      if (arr[i] !== arr_src[i] || arr_fork[i] !== arr_src[i] || arr_clk[i] !== arr_src[i]) $stop;
    end
    if (arr_elem[1] !== 8'h22) $stop;
    // With an index not known statically, so the arrays are not split into elements
    idx = $urandom_range(1, 1);
    $display("%x %x %x %x %x", arr[idx], arr_fork[idx], arr_clk[idx], arr_elem[idx], arr_src[idx]);
  end

  // Same-process NBAs commit in the order they ran (IEEE 1800-2023 10.4.2): one call's
  // trailing '<= 0' and the next call's leading '<= 1' share a time step
  typedef struct {
    int a;
    real b;
  } ord_t;
  logic ord_v = 0;
  logic [7:0] ord_pk = 0;
  real ord_r = 0;
  string ord_s = "";
  ord_t ord_st = '{0, 0};
  logic [7:0] ord_arr[4] = '{default: 0};
  int ord_idx;
  task automatic ord_pulse(int i);
    ord_v <= 1'b1;
    ord_pk[3] <= 1'b1;
    ord_r <= 1.0;
    ord_s <= "on";
    ord_st.a <= 1;
    ord_arr[i] <= 8'h1;
    ord_arr[i+1][3:0] <= 4'h1;
    #1;
    if (ord_v !== 1'b1 || ord_pk[3] !== 1'b1 || ord_r != 1.0 || ord_s != "on") $stop;
    if (ord_st.a != 1 || ord_arr[i] !== 8'h1 || ord_arr[i+1][3:0] !== 4'h1) $stop;
    ord_v <= 1'b0;
    ord_pk[3] <= 1'b0;
    ord_r <= 0.0;
    ord_s <= "off";
    ord_st.a <= 0;
    ord_arr[i] <= 8'h0;
    ord_arr[i+1][3:0] <= 4'h0;
  endtask
  initial begin
    ord_idx = $urandom_range(1, 1);
    repeat (3) ord_pulse(ord_idx);
  end

  // From an always process (#5485)
  logic ord_a = 0;
  logic ord_b = 0;
  always begin
    ord_a <= 1'b1;
    ord_a <= 1'b0;
    #1;
  end
  always begin
    ord_b <= 1'b1;
    ord_b <= 1'b0;
    #1;
    ord_b <= 1'b1;
  end
  always #1 if (ord_a !== ord_b) $stop;

endmodule
