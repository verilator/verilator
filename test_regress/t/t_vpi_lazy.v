// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

// --vpi-lazy: every signal reads as the RTL implies, before the first eval and mid-eval, and a
// put writes exactly those holding their value without a driver.

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

// A cone over the instance's own flop, read from the parent
module sub_fy (
    input logic clk,
    input logic [7:0] a
);
  /*verilator no_inline_module*/
  logic [7:0] r;
  logic [7:0] y;
  always_ff @(posedge clk) r <= a;
  assign y = r + 8'd1;
  // Refused alike in every instance: a cycle no merge can order, and an impure cone
  /* verilator lint_off UNOPTFLAT */
  logic [7:0] cyc_p, cyc_q;
  /* verilator lint_on UNOPTFLAT */
  assign cyc_p = cyc_q ^ r;
  assign cyc_q = {cyc_p[3:0], 4'h0};
  import "DPI-C" function int dpiOne();
  logic [7:0] imp_c;
  assign imp_c = r ^ 8'(dpiOne());
endmodule

// Non-ANSI ports with separate net declarations, public_flat_rw/rd after or before the port
module sub_na (
    y,
    z,
    w,
    q,
    a
);
  output y;
  wire [7:0] y;
  output z;
  wire [7:0] z  /*verilator public_flat_rw*/;
  wire [7:0] w  /*verilator public_flat_rw*/;
  output w;
  output q;
  wire [7:0] q  /*verilator public_flat_rd*/;
  input [7:0] a;
  assign y = ~a;
  assign z = a;
  assign w = a ^ 8'h0f;
  assign q = a ^ 8'hf0;
endmodule

// Writability follows the RTL name, whether or not the port is inlined.
// One-hot encoder as bsg_encode_one_hot: each level drives only some bits, reading only those.
// Literal selects, as -fno-const-before-dfg leaves a generate loop's index arithmetic unfolded.
module put_oh (
    input logic [3:0] i,
    output logic [1:0] addr_o,
    output logic v_o
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
  assign v_o = v[2][0];
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
    input logic [7:0] in_a,
    output logic [7:0] out_c,
    output logic [7:0] out_f
);

  typedef struct packed {
    logic [6:0] cnt;
    logic busy;
  } st_t;

  localparam logic [7:0] CST = 8'h3c;

  // Writable
  logic [7:0] ff_q;
  logic [7:0] arn_q;
  logic [7:0] lat_q;

  always_ff @(posedge clk) ff_q <= d;
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) arn_q <= '0;
    else arn_q <= d;
  always_latch if (en) lat_q = d;

  // Read-only
  logic [7:0] vidx[4];
  logic [7:0] cst_w;

  assign out_c = d & 8'hf0;
  always_comb vidx[sel] = d;
  assign cst_w = CST;

  // Writability must not depend on optimization flags: V3Split parts the latch from the
  // impure statement, V3Case lowers a full case as a tree or as an if/else chain, and
  // V3Const folds a parameter condition unless -fno-const-before-dfg
  logic [7:0] spl_l;
  logic [7:0] c1_c;
  logic [7:0] cg_c;
  /* verilator lint_off LATCH */
  always @* begin
    if (en) spl_l = d;
    if (never) $display("never");
  end
  /* verilator lint_on LATCH */
  always @*
    case (en)
      1'b0: c1_c = d;
      1'b1: c1_c = in_a;
    endcase
  always @*
    case (d)
      8'd0: cg_c = 8'd9;
      8'd1: cg_c = 8'd8;
      8'd2: cg_c = 8'd7;
      8'd3: cg_c = 8'd6;
      8'd4: cg_c = 8'd5;
      8'd5: cg_c = 8'd4;
      8'd6: cg_c = 8'd3;
      default: cg_c = in_a;
    endcase

  localparam bit ON = 1'b1;
  logic [7:0] pon_c;
  logic [7:0] pand_c;
  /* verilator lint_off LATCH */
  always @* if (ON || en) pon_c = d;
  always @* if (!(!ON && en)) pand_c = d;
  /* verilator lint_on LATCH */

  // Compiler temporaries keep the storage a cone reads, but no VPI name
  logic [7:0] px_o;
  wire [7:0] tw;
  logic [7:0] tw_r;
  sub u_px (
      .i(d ^ in_a),
      .o(px_o)
  );
  assign (strong0, strong1) tw = en ? d : 8'bz;
  assign (weak0, weak1) tw = in_a;
  assign tw_r = tw;

  // Mixed
  /* verilator lint_off UNOPTFLAT */
  st_t st;
  /* verilator lint_on UNOPTFLAT */
  logic [7:0] pmem[4];

  always_ff @(posedge clk) st.cnt <= st.cnt + 7'd1;
  assign st.busy = st.cnt != '0;
  assign pmem[1] = d;
  assign pmem[3] = ~d;


  // Undriven bits no read reaches hold a put; the driven ones stay the encoder's
  logic [1:0] oh_a;
  logic oh_vo;
  put_oh oh (
      .i(d[3:0]),
      .addr_o(oh_a),
      .v_o(oh_vo)
  );

  // Ports: a child's output flop is writable, the parent's net on it is not
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

  // Instances of one variable driven differently from their parent: each is writable as
  // --public-flat-rw would persist a put into it, inlined or not
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

  // Comb shapes, each read-only: chained, struct, aggregate, multiply driven
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } hl_t;
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
  } us_t;
  logic [7:0] k_q, ch1;
  hl_t hl_c;
  logic [7:0] mdp_c[2][2];
  /* verilator lint_off MULTIDRIVEN */
  wire [7:0] mixf_w, ovl_w;
  /* verilator lint_on MULTIDRIVEN */
  always_ff @(posedge clk) k_q <= d;
  assign ch1 = k_q + 8'h7;
  always_comb hl_c = d;
  // Its members' rows share its write policy
  hl_t hla_c[2];
  always_comb hla_c = '{d, ~d};
  always_comb begin
    mdp_c[0][0] = d;
    mdp_c[0][1] = in_a;
    mdp_c[1] = '{~d, ~in_a};
  end
  assign mixf_w = k_q;
  assign mixf_w[2:0] = in_a[2:0];
  assign ovl_w[4:0] = k_q[4:0];
  assign ovl_w[7:2] = in_a[5:0];
  // Aliases whose rows carry their own range, sign or bit type
  logic signed [8:1] al_sw;
  bit [7:0] sib_bt;
  assign al_sw = k_q;
  assign sib_bt = ch1;
  // A fold row, and a sibling of another row on the same cone
  logic [7:0] fold_c, fmid_c, sib_b;
  always_comb fold_c = d ^ 8'h3c;
  always_comb fmid_c = fold_c;
  assign sib_b = ch1;

  // Latches per bit: the bits some path through an if-tree leaves unassigned take a put
  logic [7:0] plo_l;
  /* verilator lint_off LATCH */
  always @*
    if (1'b0) plo_l[7:6] = d[7:6];
    else if (en) plo_l[5:0] = d[5:0];
    else plo_l[7:2] = in_a[7:2];
  /* verilator lint_on LATCH */

  sub_na u_na (
      .y(),
      .z(),
      .w(),
      .q(),
      .a(d)
  );

  // Each a cone reading another instance's cone, which refreshes that instance
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
  logic [7:0] fyx1b_c;
  assign fyx1b_c = fy1.y + 8'h01;

  // Statement shapes a cone refuses or keeps: a read before its write; a dead store in a loop
  // left by a break; an unpacked struct member lvalue; an impure continuous assign
  /* verilator lint_off UNOPTFLAT */
  logic [7:0] rbw_t, rbw_c, rbw_u, rbw_v, dlp_c, dus_c;
  /* verilator lint_on UNOPTFLAT */
  logic [7:0] dlp_t  /*verilator public_flat_rw*/;
  logic [31:0] rnd_w, seedv;
  us_t dus;
  /* verilator lint_off ALWCOMBORDER */
  always_comb begin
    rbw_c = rbw_t;
    rbw_t = d | in_a;
    if (sel[0]) begin
      rbw_u = rbw_c;
      rbw_v = in_a;
    end else begin
      rbw_u = in_a;
      rbw_v = rbw_c;
    end
  end
  /* verilator lint_on ALWCOMBORDER */
  always_comb begin
    dlp_c = d ^ 8'h3;
    for (int i = 0; i < int'(sel); ++i) begin
      if (d[1]) break;
      dlp_t = dlp_c + 8'h1;
    end
  end
  always_comb begin
    dus_c = d + 8'h6;
    dus.a = dus_c;
    dus.b = ~dus_c;
  end
  assign rnd_w = $urandom(seedv);

  // A comb signal kept in storage, as its impure driver can't be rebuilt, read from a flop and
  // sampled by one
  import "DPI-C" function int dpiOne();
  logic [7:0] ret_c, ret_q;
  always_comb ret_c = k_q ^ 8'(8'h5a * dpiOne());
  always_ff @(posedge clk) ret_q <= ret_c;

  // A cone read twice from one eval, its input moved between the reads
  logic [7:0] mid_s, mid_c;
  assign mid_c = mid_s + 8'h1;
  // A cone read mid-eval, its source put between evals
  logic [7:0] prb_s, prb_c;
  assign prb_c = prb_s ^ 8'h3c;
  import "DPI-C" context function void midEvalProbe();
  import "DPI-C" context function void midEvalRead(int src);
  always @(posedge clk) midEvalProbe();
  initial begin
    mid_s = 8'h10;
    midEvalRead(int'(mid_s));
    mid_s = 8'h20;
    midEvalRead(int'(mid_s));
  end

  // A cone nested past _complimit's --comp-limit-blocks, over a function's temporaries
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

  // A constant select read before its write, which a cone refuses, and a branch both constant
  // operands of which hold under -fno-const-before-dfg, which it takes
  /* verilator lint_off UNOPTFLAT */
  logic [7:0] rbs_c;
  /* verilator lint_on UNOPTFLAT */
  /* verilator lint_off ALWCOMBORDER */
  always_comb begin
    rbs_c[7:4] = rbs_c[3:0] ^ d[7:4];
    rbs_c[3:0] = d[3:0];
  end
  /* verilator lint_on ALWCOMBORDER */
  logic [7:0] ct_c;
  always_comb begin
    if (1'b1 && 1'b1) ct_c = d;
    else ct_c = in_a;
  end

  // Arms defining different elements and variables, and an else holding an if and more
  logic [7:0] am_m[2];
  logic [7:0] am_x, am_z, ae_c, ae_f, ae_g;
  always_comb begin
    am_m[0] = 8'h0;
    am_x = 8'h0;
    am_z = 8'h0;
    if (sel[0]) begin
      am_m[0] = d;
      am_m[1] = in_a;
      am_x = d;
    end else begin
      am_m[1] = d;
      am_z = in_a;
    end
  end
  always_comb begin
    ae_f = 8'h0;
    ae_g = 8'h0;
    if (sel[1]) ae_c = d;
    else begin
      if (d[0]) begin
        ae_c = in_a;
        ae_f = d;
      end else ae_c = 8'h0;
      ae_g = in_a;
    end
  end
  // Written whole by one block and in part by another
  logic [3:0] vbx;
  assign vbx[sel] = en;
  always_comb vbx[3:2] = d[1:0];

  // A cycle between groups, not bits, merged with a function's temporaries (under -O0, as
  // V3BitBlast otherwise splits it)
  /* verilator lint_off UNOPTFLAT */
  logic [1:0][3:0] mc_x;
  logic [3:0] mc_y;
  /* verilator lint_on UNOPTFLAT */
  assign mc_x[0] = d[3:0];
  always_comb mc_y = 4'(nest_f({4'h0, mc_x[0]}));
  assign mc_x[1] = mc_y;

  // Its undriven element read by the design, so retained with storage
  logic [7:0] gmem[2];
  logic [7:0] gmem_r;
  assign gmem[1] = d;
  assign gmem_r = gmem[0];

  // A forceable alias of a top input
  logic [7:0] frc_al  /*verilator forceable*/;
  assign frc_al = in_a;

  // A cycle between groups in two scopes
  /* verilator lint_off UNOPTFLAT */
  logic [7:0] xc_x, xc_y;
  /* verilator lint_on UNOPTFLAT */
  sub_xc u_xc (
      .i(xc_x),
      .o(xc_y)
  );
  assign xc_x = {d[7:4], xc_y[7:4]};

  // Copies of a source stored in one instance and a cone in the other
  sub_cpy cpy0 ();
  sub_cpy cpy1 ();
  always_ff @(posedge clk) cpy0.m <= d;
  assign cpy1.m = d ^ in_a;

  // An interface written through its modport by a child, a cone over $random, and a module
  // copying its input twice, instanced over a stored and a comb source
  logic [7:0][7:0] sh;
  logic [7:0][7:0] sw_o;
  always_ff @(posedge clk) sh <= {sh[6:0], d};
  swap_if intf ();
  assign intf.wdata = sh;
  assign sw_o = intf.swapped;
  sub_ifwrite u_ifwrite (intf);
  logic [7:0] rndc;
  always_comb rndc = 8'(d[3:0]) + 8'($random);
  bit [7:0] pull_b;
  logic [7:0] pull_w, pull_o0, pull_o1, pull_x;
  always_ff @(posedge clk) pull_b <= d ^ 8'h3c;
  assign pull_w = pull_b;
  pull_mod u_pull0 (
      .pi(pull_w),
      .po(pull_o0)
  );
  assign pull_x = in_a ^ d;
  pull_mod u_pull1 (
      .pi(pull_x),
      .po(pull_o1)
  );

  // Real and string cones and copies, a formatted string, and rows a mask cannot name bits of
  real r_comb, rc_src, rf_mid;
  string s_fmt, sc_src, sc_alias;
  real ra_c[2];
  real ra_s;
  always_comb r_comb = 1.5;
  always_comb s_fmt = $sformatf("v%0d", d);
  always_ff @(posedge clk) begin
    rc_src <= $itor(d) + 0.5;
    if (d[0]) sc_src <= "odd";
    else sc_src <= "even";
  end
  always_comb sc_alias = sc_src;
  always_comb rf_mid = r_comb;
  assign ra_c[0] = 1.5;
  always_comb ra_c[1] = rc_src;
  assign ra_s = ra_c[0] + ra_c[1];
  /* verilator lint_off SELRANGE */
  /* verilator lint_off WIDTHTRUNC */
  logic [7:0] oor_c, oor_r;
  assign oor_c[9:6] = d[3:0];
  assign oor_c[5:0] = in_a[5:0];
  assign oor_r = oor_c ^ 8'h0f;
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on SELRANGE */

  // A memory assembled from its own elements, and its copy in the opposite range, which slices
  // into one continuous assign per element, all in one block
  logic [7:0] mem_chain[0:2];
  logic [7:0] mem_rev[2:0];
  always_comb begin
    mem_chain[0] = d;
    mem_chain[1][3:0] = mem_chain[0][7:4];
    mem_chain[1][7:4] = mem_chain[1][3:0] ^ in_a[3:0];
    mem_chain[2] = mem_chain[1] + 8'd1;
  end
  assign mem_rev = mem_chain;

  // Undriven, so a put is its only source
  logic [7:0] orphan;
  logic [7:0] orphan_c;
  assign orphan_c = orphan ^ 8'h0f;

  // Forced by SV force/release though not forceable
  logic [6:0] keep_frc;
  logic [6:0] frc2;
  always_ff @(posedge clk) keep_frc <= rst ? 7'h0 : keep_frc + 7'h3;
  assign frc2 = keep_frc + 7'h22;
  always @(posedge clk) begin
    if (d == 8'h3c) force frc2 = 7'h55;
    else release frc2;
  end

  // A case arm writing part of a variable its default writes whole
  logic [6:0] keep;
  logic signed [6:0] skeep;
  logic [6:0] cf_casepart;
  always_ff @(posedge clk) begin
    keep <= rst ? 7'h0 : keep + 7'h3;
    skeep <= rst ? 7'sh0 : skeep - 7'sd2;
  end
  always_comb begin
    cf_casepart = keep;
    case (keep[1:0])
      2'd0: cf_casepart = keep + 7'h1;
      2'd1: cf_casepart[3:0] = skeep[3:0];
      default: cf_casepart = ~keep;
    endcase
  end

  // A forceable unpacked array chained through itself
  wire [64:0] fa[2]  /* verilator forceable */;
  wire [64:0] fb[2];
  assign fa[0] = {57'h1_2345_6789_abcd, d};
  assign fa[1] = fb[0];
  assign fb = fa;

  // Sections, each over the clock and the inputs above
  lz_multi u_mi (
      .clk,
      .rst,
      .din(d)
  );
  lz_order u_po (
      .clk,
      .fo(out_f)
  );
endmodule

module sub_xc (
    input logic [7:0] i,
    output logic [7:0] o
);
  /*verilator no_inline_module*/
  assign o = i ^ 8'h01;
endmodule

module sub_cpy;
  /*verilator no_inline_module*/
  logic [7:0] m;
  logic [7:0] c;
  assign c = m;
endmodule

interface swap_if #(
    parameter int DBW = 8
) ();
  logic [DBW-1:0][7:0] wdata;
  logic [DBW-1:0][7:0] swapped;
  function automatic logic [DBW-1:0][7:0] swap_endianness(logic [DBW-1:0][7:0] input_value);
    integer i;
    logic [DBW-1:0][7:0] input_value_swapped;
    for (i = 0; i < DBW; i++) input_value_swapped[DBW-1-i] = input_value[i];
    return input_value_swapped;
  endfunction
  modport slave(input wdata, output swapped, import swap_endianness);
endinterface

module sub_ifwrite (
    swap_if.slave s
);
  always_comb s.swapped = s.swap_endianness(s.wdata);
endmodule

module pull_leaf (
    input logic [7:0] d,
    output logic [7:0] q
);
  assign q = d ^ 8'h0f;
endmodule

module pull_mod (
    input logic [7:0] pi,
    output logic [7:0] po
);
  /*verilator no_inline_module*/
  logic [7:0] pi_cast;
  logic [7:0] pi_cp;
  assign pi_cast = pi;
  assign pi_cp = pi_cast;
  pull_leaf u_leaf (
      .d(pi_cp),
      .q(po)
  );
endmodule

interface iface2_mi;
  logic [6:0] a;
  logic [6:0] b;
  logic [6:0] s;  // Undriven but read in if1, which keeps its storage apart from if0's cone
endinterface

module child (
    input logic clk,
    input logic [7:0] din
);
  /*verilator no_inline_module*/
  logic [7:0] cflop;
  always_ff @(posedge clk) cflop <= din ^ 8'h5a;
  // Driven in part alike in both instances, so they share one comb mask
  logic [7:0] cpart;
  assign cpart[3:0] = din[3:0];
endmodule

// Driven only by cross-scope assigns in the parent
module bcell;
  /*verilator no_inline_module*/
  logic [7:0] bc;
  logic [7:0] bx, by;
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

module lz_multi (
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

  logic [7:0] bflop0, bflop1;
  always_ff @(posedge clk) begin
    bflop0 <= din ^ 8'ha5;
    bflop1 <= din ^ 8'h5a;
  end
  bcell bc0 ();
  bcell bc1 ();
  assign bc0.bc = bflop0;
  assign bc1.bc = bflop1;
  always_comb begin
    automatic logic [7:0] tmp = bflop0 + 8'h1;
    bc0.bx = tmp;
    bc0.by = tmp ^ 8'h3;
  end
  assign {bc1.bx, bc1.by} = {bflop1, ~bflop1};
endmodule

// From put order: puts into real, string and forceable sources, and mid-eval puts
module lz_order (
    input logic clk,
    output logic [7:0] fo
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
  // A top output's copy, which must not make f continuously assigned
  assign fo = f;
  import "DPI-C" context function void midEvalPut(string name, int v);
  // A put between two reads of the same condition reaches the second
  logic mcnd;
  logic [7:0] mc_a, mc_b;
  initial begin
    midEvalPut("t.u_po.mcnd", 1);
    mc_a = mcnd ? 8'h01 : 8'h02;
    midEvalPut("t.u_po.mcnd", 0);
    mc_b = mcnd ? 8'h03 : 8'h04;
  end
  // Read by a DPI export, which pins its storage
  export "DPI-C" function t_mc_b;
  function int t_mc_b();
    return int'(mc_b);
  endfunction
  // A flop only a DPI export reads, and its comb reader
  logic [7:0] xq;
  always_ff @(posedge clk) xq <= s;
  wire [7:0] xq_c = xq + 8'h1;
  export "DPI-C" function t_xq;
  function int t_xq();
    return int'(xq);
  endfunction
endmodule

`ifdef T_VPI_LAZY_SAVABLE
// The top t_vpi_lazy_savable saves and restores, as --savable takes no forceable or unpacked
// struct signal
module lz_save (
    input logic clk
);
  logic [7:0] d, k_q, ch1, al1;
  always_ff @(posedge clk) k_q <= d;
  assign ch1 = k_q + 8'h7;
  assign al1 = k_q;
  lz_trace u_tr ();
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(1, u_tr);
  end
endmodule

// From comb trace: an initial-only variable, its copy, a cone, and the cone's own copy and reader
module lz_trace;
  logic [6:0] keep;
  logic [6:0] cmb;
  logic [6:0] alias1;
  wire [6:0] cmb_net;
  wire [6:0] cmb_ali;
  logic [6:0] obs;
  initial keep = 7'h2d;
  assign cmb = keep + 7'h1;
  assign alias1 = keep;
  assign cmb_net = cmb ^ 7'h55;
  assign cmb_ali = cmb;
  assign obs = keep ^ alias1 ^ cmb_net ^ cmb_ali;
endmodule
`endif
