// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// '$c(1)' keeps an expression impure so the compiler cannot precompute it.
`ifdef VERILATOR
`define IMPURE_ONE ($c(1))
`else
`define IMPURE_ONE (1)
`endif

module t (
    input logic [7:0] in_a
);

  logic clk = 1'b0;
  always #5 clk = ~clk;

  // cyc steps the puts
  logic [7:0] cyc = 8'h0;
  logic rst;
  assign rst = cyc < 8'd2;
  always @(posedge clk) begin
    cyc <= cyc + 8'h1;
    if (cyc == 8'd13) begin
      $write("*-* All Finished *-*\n");
      #1 $finish;
    end
  end

  import "DPI-C" context function void t_vpi_dump_value(input string name);
  import "DPI-C" context function void t_vpi_dump_put(
    input string name,
    input string value
  );
  import "DPI-C" context function void t_vpi_dump_values();
  import "DPI-C" context function void t_vpi_dump_cb(input string name);
  import "DPI-C" context function void t_vpi_dump_put_rw(
    input string name,
    input string value,
    input string flag = ""
  );

  initial begin
    t_vpi_dump_cb("t.s_comb");
    t_vpi_dump_cb("t.cyc");
    t_vpi_dump_cb("t.watched");
    t_vpi_dump_put("t.in_a", "00");
    t_vpi_dump_values();
  end
  always @(clk) t_vpi_dump_values();
  always @(cyc) begin
    case (cyc)
      8'd2: t_vpi_dump_put_rw("t.in_a", "11");
      8'd4: begin
        t_vpi_dump_put_rw("t.s", "22");
        t_vpi_dump_put_rw("t.in_a", "33");
        t_vpi_dump_put_rw("t.mem[1]", "44");
        t_vpi_dump_put_rw("t.r", "real=4.0");
        t_vpi_dump_put_rw("t.str", "str=longer_than_any_short_string_buffer");
      end
      8'd5: t_vpi_dump_put_rw("t.s", "55");
      8'd6: t_vpi_dump_put_rw("t.s", "77", "inertial");
      8'd7: t_vpi_dump_put_rw("t.f", "55", "force");
      8'd8: t_vpi_dump_put_rw("t.f", "66", "release");
      8'd9: t_vpi_dump_put_rw("t.s", "5c");
      8'd11: begin
        t_vpi_dump_put_rw("t.init_only", "31");
        t_vpi_dump_put_rw("t.undriven", "32");
        t_vpi_dump_put_rw("t.once", "33");
        t_vpi_dump_put_rw("t.part", "a3");
      end
      default: ;
    endcase
  end

  // 'dep' is combinationally driven from an impure expression, and sampled by a flop
  logic [7:0] src = 8'h0;
  logic [7:0] dep;
  logic [7:0] dep_obs;
  logic [7:0] dep_q = 8'h0;
  always_comb dep = src ^ 8'(8'h5a * `IMPURE_ONE);
  always_comb dep_obs = dep + 8'(8'h01 * `IMPURE_ONE);

  // A combinational signal sampled from DPI during eval, after its input moved
  logic [7:0] cnt = 8'h0;
  logic [7:0] tri3;
  assign tri3 = cnt * 8'd3;
  // cnt does not change at time 0, but this runs then under Verilator (IEEE 1800-2023 9.4.2)
  always @(cnt) if (cnt != 8'h0) t_vpi_dump_value("t.tri3");

  // cbValueChange on a combinational signal whose input a put writes when it changes
  logic [7:0] cin = 8'h0;
  logic [7:0] watched;
  assign watched = cin + 8'd7;
  always @(watched) if (watched == 8'h0f) t_vpi_dump_put_rw("t.cin", "40");

  // A put reaches a combinational reader only at the next eval
  logic [7:0] s = 8'h0;
  logic [7:0] s_q = 8'h0;
  logic [7:0] mem[2] = '{default: 8'h0};
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
  logic [7:0] f  /*verilator forceable*/ = 8'h0;
  wire [7:0] f_comb = f ^ 8'h0f;

  // A put into bits no process drives reaches their readers at the next eval
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
  // Only under Verilator, so cmid and cmid_seen stay X elsewhere
`ifdef VERILATOR
  initial begin
    cmid = 8'h00;
    $c("t_vpi_dump_put(\"t.cmid\", \"5b\");");
    cmid_seen = cmid;
  end
`endif

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
