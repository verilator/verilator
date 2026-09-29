// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// '$c(1)' keeps an expression impure so the compiler cannot precompute it.
`define IMPURE_ONE ($c(1))

module t (
    input logic [7:0] in_a
);

  logic clk = 1'b0;
  always #5 clk = ~clk;

  // cyc steps the harness puts
  logic [7:0] cyc = 8'h0;
  logic rst;
  assign rst = cyc < 8'd2;
  always @(posedge clk) begin
    cyc <= cyc + 8'h1;
    if (cyc == 8'd13) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  import "DPI-C" context function void t_vpi_dump_value(input string name);
  import "DPI-C" context function void t_vpi_dump_put(
    input string name,
    input string value
  );

  // 1: 'dep' is combinationally driven from an impure expression, and sampled by a flop
  logic [7:0] src;
  logic [7:0] dep;
  logic [7:0] dep_obs;
  logic [7:0] dep_q;
  always_comb dep = src ^ 8'(8'h5a * `IMPURE_ONE);
  always_comb dep_obs = dep + 8'(8'h01 * `IMPURE_ONE);

  // 2: a combinational signal sampled from DPI during eval, after its input moved
  logic [7:0] cnt;
  logic [7:0] tri3;
  assign tri3 = cnt * 8'd3;
  always @(cnt) t_vpi_dump_value("t.tri3");

  // 3: cbValueChange on a combinational signal whose input the callback writes
  logic [7:0] cin;
  logic [7:0] watched;
  assign watched = cin + 8'd7;

  // 4: a put reaches a combinational reader only at the next eval
  logic [7:0] s;
  logic [7:0] s_q;
  logic [7:0] mem[2];
  wire [7:0] s_comb = s ^ 8'h5a;
  wire [7:0] s_copy = s;
  wire [7:0] s_dup = s_comb;
  logic [7:0] s_sum;
  always_comb s_sum = s + 8'(8'h02 * `IMPURE_ONE);
  wire [7:0] s_mix = s_sum ^ s;
  wire [7:0] in_comb = in_a + 8'd3;
  wire [7:0] mem_comb = mem[1] ^ 8'hf0;
  real r = 1.5;
  real r_comb;
  assign r_comb = r * 2.0;
  string str = "ab";
  string str_comb;
  assign str_comb = {str, "!"};
  logic [7:0] f  /*verilator forceable*/;
  wire [7:0] f_comb = f ^ 8'h0f;
  // 6: a put into bits no process drives reaches their readers at the next eval
  logic [7:0] init_only;
  logic [7:0] undriven;
  logic [7:0] once = 8'h21;
  logic [7:0] part;
  logic [7:0] mid;
  logic [7:0] mid_seen;
  logic [7:0] cmid;
  logic [7:0] cmid_seen;
  initial init_only = 8'h11;
  assign part[3:0] = in_a[3:0];
  wire [7:0] init_comb = init_only ^ 8'h0f;
  wire [7:0] und_comb = undriven ^ 8'h0f;
  wire [7:0] once_comb = once ^ 8'h0f;
  wire [3:0] part_comb = part[7:4] ^ 4'h3;
  logic [7:0] init_sum;
  logic [7:0] und_sum;
  always_comb init_sum = init_only + 8'(8'h01 * `IMPURE_ONE);
  always_comb und_sum = undriven + 8'(8'h01 * `IMPURE_ONE);
  initial begin
    mid = 8'h00;
    t_vpi_dump_put("t.mid", "5a");
    mid_seen = mid;
  end
  initial begin
    cmid = 8'h00;
    $c("t_vpi_dump_put(\"t.cmid\", \"5b\");");
    cmid_seen = cmid;
  end

  always_ff @(posedge clk) begin
    s <= in_a;
    s_q <= s;
    mem[0] <= s;
    mem[1] <= in_a;
    f <= in_a + 8'd1;
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      src <= 8'h0;
      dep_q <= 8'h0;
      cnt <= 8'h0;
      cin <= 8'h0;
    end
    else begin
      src <= src + 8'h1;
      dep_q <= dep;
      cnt <= cnt + 8'h1;
      cin <= cin + 8'h1;
    end
  end

endmodule
