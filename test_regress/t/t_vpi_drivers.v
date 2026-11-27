// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop

// Each signal a driver shape, read and written through VPI.

module sub (
    input logic [7:0] i,
    output logic [7:0] o
);
  assign o = ~i;
endmodule

module sub_ff (
    input logic clk,
    input logic [7:0] d,
    output logic [7:0] q
);
  always_ff @(posedge clk) q <= d;
endmodule

module sub_mix (
    input logic clk,
    input logic en,
    input logic [7:0] d,
    output logic [7:0] m
);
  always_ff @(posedge clk) m[7:1] <= d[7:1];
  assign m[0] = en;
endmodule

interface ifc;
  logic [7:0] q;
endinterface

module sub_if (
    input logic clk,
    input logic [7:0] d,
    ifc bus
);
  always_ff @(posedge clk) bus.q <= d;
endmodule

interface ifc_pair;
  logic [7:0] q;
endinterface

module sub_st;
  logic [7:0] p;
endmodule

module sub_ni;
  /*verilator no_inline_module*/
  logic [7:0] m;
endmodule

// Comb logic over the instance's own flop, read from the parent
module sub_fy (
    input logic clk,
    input logic [7:0] a
);
  /*verilator no_inline_module*/
  logic [7:0] r;
  logic [7:0] y;
  always_ff @(posedge clk) r <= a;
  assign y = r + 8'd1;
endmodule

// Non-ANSI ports with separate net declarations, public_flat_rw after or before the port
module sub_na (
    z,
    w,
    a
);
  output z;
  wire [7:0] z  /*verilator public_flat_rw*/;
  wire [7:0] w  /*verilator public_flat_rw*/;
  output w;
  input [7:0] a;
  assign z = a;
  assign w = a ^ 8'h0f;
endmodule

// One-hot encoder as bsg_encode_one_hot: each level drives only some bits, reading only those.
module put_oh (
    input logic [3:0] i,
    output logic [1:0] addr_o
);
  /* verilator lint_off UNOPTFLAT */
  logic [2:0][3:0] addr;
  logic [2:0][3:0] v;
  logic [1:0] vs10, vs12, vs20;
  /* verilator lint_on UNOPTFLAT */
  assign v[0] = i;
  assign addr[0] = '0;
  assign vs10 = {v[0][1], v[0][0]};
  assign vs12 = {v[0][3], v[0][2]};
  assign v[1][0] = |vs10;
  assign v[1][2] = |vs12;
  assign addr[1][0] = vs10[1];
  assign addr[1][2] = vs12[1];
  assign vs20 = {v[1][2], v[1][0]};
  assign v[2][0] = |vs20;
  assign addr[2][1:0] = {vs20[1], addr[1][0] | addr[1][2]};
  assign addr_o = addr[2][1:0];
endmodule

module t #(
    parameter int INTF_QTY = 3
) (
    input logic clk,
    input logic rst,
    input logic rst_n,
    input logic en,
    input logic never,
    input logic [1:0] sel,
    input logic [7:0] d,
    input logic [7:0] in_a
);

  typedef struct packed {
    logic [6:0] cnt;
    logic busy;
  } st_t;

  // Flops and latches
  logic [7:0] ff_q;
  logic [7:0] arn_q;
  logic [7:0] lat_q;
  logic [6:0] spl_l;

  always_ff @(posedge clk) ff_q <= d;
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) arn_q <= '0;
    else arn_q <= d;
  always_latch if (en) lat_q = d;
  // A latch beside an impure statement
  /* verilator lint_off LATCH */
  always @* begin
    if (en) spl_l = d[6:0];
    if (never) $display("never");
  end
  /* verilator lint_on LATCH */

  // Comb logic over an instance's input port expression and over a strength-resolved net
  logic [7:0] px_o;
  wire [6:0] tw;
  logic [6:0] tw_r;
  sub u_px (
      .i(d ^ in_a),
      .o(px_o)
  );
  assign (strong0, strong1) tw = en ? d[6:0] : 7'bz;
  assign (weak0, weak1) tw = in_a[6:0];
  assign tw_r = tw;

  // Driven in part by a flop or memory, in part by comb logic
  /* verilator lint_off UNOPTFLAT */
  st_t st;
  /* verilator lint_on UNOPTFLAT */
  logic [7:0] pmem[4];

  always_ff @(posedge clk) st.cnt <= st.cnt + 7'd1;
  assign st.busy = st.cnt != '0;
  assign pmem[1] = d;
  assign pmem[3] = ~d;

  logic [1:0] oh_a;
  put_oh oh (
      .i(d[3:0]),
      .addr_o(oh_a)
  );

  // Wide comb logic, read whole across word boundaries
  logic [32:0] w33_c;
  logic [64:0] w65_c;
  logic [94:0] w95_c;
  assign w33_c = {d[0], {4{d ^ in_a}}};
  assign w65_c = {w33_c[31:0], w33_c} ^ {in_a, 57'h0};
  assign w95_c = {w65_c[29:0], ~w65_c};

  // Wide variables a flop drives in part
  logic [32:0] wm33;
  logic [64:0] wm65;
  logic [94:0] wm95;
  always_ff @(posedge clk) begin
    wm33[31:0] <= {4{d}};
    wm65[64:41] <= {3{d}};
    wm65[27:0] <= {d[3:0], {3{in_a}}};
    wm95[94:71] <= {3{in_a}};
    wm95[59:0] <= {d[3:0], {7{d}}};
  end
  assign wm33[32] = ^d;
  assign wm65[40:28] = {d[4:0], in_a};
  assign wm95[70:60] = {d[2:0], in_a};

  // Ports: a child's output flop and the parent's net on it
  logic [7:0] w_ff;
  logic [7:0] w_mix;
  logic [7:0] n_ff;
  logic [7:0] n_mix;
  logic [7:0] n_if;
  ifc bus ();

  sub_ff u_ff (
      .clk,
      .d,
      .q(w_ff)
  );
  sub_mix u_mix (
      .clk,
      .en,
      .d,
      .m(w_mix)
  );
  sub_if u_if (
      .clk,
      .d,
      .bus
  );
  always_ff @(posedge clk) begin
    n_ff <= w_ff;
    n_mix <= w_mix;
    n_if <= bus.q;
  end

  // Instances of one variable driven differently from their parent
  logic [7:0] n_ia;
  logic [7:0] n_mc2;
  ifc_pair ia ();
  ifc_pair ib ();
  always_ff @(posedge clk) ia.q <= d;
  assign ib.q = ia.q;
  sub_st cp ();
  assign cp.p[3:0] = d[3:0];
  sub_ni mc0 ();
  sub_ni mc1 ();
  sub_ni mc2 ();
  assign mc0.m[3:0] = d[3:0];
  assign mc1.m[7:4] = in_a[7:4];
  always_ff @(posedge clk) mc2.m <= d;
  always_ff @(posedge clk) begin
    n_ia <= ia.q;
    n_mc2 <= mc2.m;
  end

  // Comb shapes: chained, struct, aggregate
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } hl_t;
  logic [7:0] k_q, ch1;
  hl_t hl_c;
  always_ff @(posedge clk) k_q <= d;
  assign ch1 = k_q + 8'h7;
  always_comb hl_c = d;
  hl_t hla_c[2];
  always_comb hla_c = '{d, ~d};
  // Aliases whose rows carry their own range, sign or bit type
  logic signed [8:1] al_sw;
  bit [7:0] sib_bt;
  assign al_sw = k_q;
  assign sib_bt = ch1;
  // A plain copy of a comb signal, and a second copy of a signal another row copies
  logic [8:0] fold_c, fmid_c;
  logic [7:0] sib_b;
  always_comb fold_c = 9'(d) ^ 9'h13c;
  always_comb fmid_c = fold_c;
  assign sib_b = ch1;

  sub_na u_na (
      .z(),
      .w(),
      .a(d)
  );

  // Each comb logic reading another instance's comb signal
  logic [7:0] fyx0_c, fyx1_c;
  sub_fy fy0 (
      .clk(clk),
      .a(d)
  );
  sub_fy fy1 (
      .clk(clk),
      .a(~d)
  );
  assign fyx0_c = fy0.y ^ 8'h55;
  assign fyx1_c = fy1.y ^ 8'h55;

  // An unpacked struct member a flop holds, beside one undriven
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
  } us_t;
  us_t fus;
  always_ff @(posedge clk) fus.a <= d;

  // A comb signal with an impure driver, sampled by a flop
  import "DPI-C" function int dpiOne();
  logic [7:0] ret_c, ret_q;
  always_comb ret_c = k_q ^ 8'(8'h5a * dpiOne());
  always_ff @(posedge clk) ret_q <= ret_c;

  // A part select read mid-eval, overwritten after the read
  /* verilator lint_off UNOPTFLAT */
  logic [7:0] pk_c;
  /* verilator lint_on UNOPTFLAT */
  import "DPI-C" context function void midEvalPeek(
    string name,
    int want,
    int mask
  );
  /* verilator lint_off ALWCOMBORDER */
  always_comb begin
    pk_c[7:4] = pk_c[3:0] ^ d[7:4];
    pk_c[3:0] = 4'h5;
    midEvalPeek("t.pk_c", 'h5, 'hf);
    pk_c[3:0] = d[3:0];
  end
  /* verilator lint_on ALWCOMBORDER */

  // Deeply nested comb logic over a function's temporaries
  function automatic logic [7:0] nest_f(input logic [7:0] v);
    nest_f = v + 8'd3;
  endfunction
  logic [7:0] nest_c;
  always_comb begin
    nest_c = 8'h0;
    if (sel[0]) begin
      if (d[0]) begin
        if (in_a[6]) nest_c = nest_f(d) ^ nest_f(in_a);
      end
    end
  end

  // A branch on two constant operands
  logic [14:0] ct_c;
  always_comb begin
    if (1'b1 && 1'b1) ct_c = 15'(d);
    else ct_c = 15'(in_a);
  end

  // A cycle between whole vectors, not their bits, through a function's temporaries
  /* verilator lint_off UNOPTFLAT */
  logic [1:0][3:0] mc_x;
  logic [3:0] mc_y;
  /* verilator lint_on UNOPTFLAT */
  assign mc_x[0] = d[3:0];
  always_comb mc_y = 4'(nest_f({4'h0, mc_x[0]}));
  assign mc_x[1] = mc_y;

  // Its undriven element read by the design
  logic [7:0] gmem[2];
  logic [7:0] gmem_r;
  assign gmem[1] = d;
  assign gmem_r = gmem[0];

  // A forceable alias of a top input
  logic [7:0] frc_al  /*verilator forceable*/;
  assign frc_al = in_a;

  // A memory assembled from its own elements in one block
  logic [7:0] mem_chain[0:2];
  always_comb begin
    mem_chain[0] = d;
    mem_chain[1][3:0] = mem_chain[0][7:4];
    mem_chain[1][7:4] = mem_chain[1][3:0] ^ in_a[3:0];
    mem_chain[2] = mem_chain[1] + 8'd1;
  end

  // Undriven, so a put is its only source
  logic [7:0] orphan;
  logic [7:0] orphan_c;
  assign orphan_c = orphan ^ 8'h0f;

  sub_multi u_mi (
      .clk,
      .rst,
      .din(d)
  );
  sub_order u_po (.clk);

  // The driver finishes; a pending event keeps --binary's main running until it does
  initial begin
    #1000;
    $write("%%Error: timeout\n");
    `stop;
  end
endmodule

interface iface2_mi;
  logic [6:0] a;
  logic [6:0] b;
  logic [6:0] s;  // Undriven, but read in if1 and comb-driven in if0
endinterface

module child (
    input logic clk,
    input logic [7:0] din
);
  /*verilator no_inline_module*/
  logic [7:0] cflop;
  always_ff @(posedge clk) cflop <= din ^ 8'h5a;
endmodule

module parent (
    input logic clk,
    input logic [7:0] din
);
  /*verilator no_inline_module*/
  child uc (
      .clk(clk),
      .din(din)
  );
  logic [7:0] xali;
  assign xali = uc.cflop;
endmodule

module sub_multi (
    input logic clk,
    input logic rst,
    input logic [7:0] din
);
  logic [6:0] ctr;
  always_ff @(posedge clk) ctr <= rst ? 7'h0 : ctr + 7'h3;

  iface2_mi if0 ();
  iface2_mi if1 ();
  assign if0.a = ctr;
  assign if1.a = ctr + 7'h1;
  assign if0.b = ~if0.a;
  assign if1.b = if1.a ^ 7'h55;
  assign if0.s = ctr + 7'h9;
  logic [6:0] observe2;
  always_ff @(posedge clk) observe2 <= if0.b ^ if1.b ^ if1.s;

  parent p0 (
      .clk(clk),
      .din(din)
  );
  parent p1 (
      .clk(clk),
      .din(din + 8'h40)
  );
endmodule

// Puts into real, string and forceable sources, and mid-eval puts
module sub_order (
    input logic clk
);
  logic [7:0] s;
  wire [7:0] s_comb = s ^ 8'h5a;
  real r;
  real r_comb;
  assign r_comb = r * 2.0;
  string str;
  string str_comb;
  assign str_comb = {str, "!"};
  logic [7:0] f  /*verilator forceable*/;
  wire [7:0] f_comb = f ^ 8'h0f;
  always_ff @(posedge clk) f <= s + 8'd1;
  import "DPI-C" context function void midEvalPut(
    string name,
    int v
  );
  // A put between two reads of the same condition reaches the second
  logic mcnd;
  logic [7:0] mc_a, mc_b;
  initial begin
    midEvalPut("t.u_po.mcnd", 1);
    mc_a = mcnd ? 8'h01 : 8'h02;
    midEvalPut("t.u_po.mcnd", 0);
    mc_b = mcnd ? 8'h03 : 8'h04;
  end
  // A flop only a DPI export reads, and its comb reader
  logic [7:0] xq;
  always_ff @(posedge clk) xq <= s;
  wire [7:0] xq_c = xq + 8'h1;
  export "DPI-C" function t_xq;
  function int t_xq();
    return int'(xq);
  endfunction
endmodule
