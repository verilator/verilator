// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Which signals a VPI put may write under --vpi-lazy: those holding their value without a driver.

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

interface ifc_cons;
  logic [7:0] sig;
  modport cons(input sig);
endinterface

module sub_cons (
    input logic clk,
    ifc_cons.cons bus,
    output logic [7:0] cap
);
  always_ff @(posedge clk) cap <= bus.sig;
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

module sub_pass (
    /* verilator lint_off UNOPTFLAT */
    input logic [7:0] i,
    /* verilator lint_on UNOPTFLAT */
    /* verilator lint_off MULTIDRIVEN */
    output logic [7:0] o
    /* verilator lint_on MULTIDRIVEN */
);
  assign o = i;
endmodule

module sub_cy (
    input logic [7:0] din
);
  /*verilator no_inline_module*/
  logic [7:0] cy;
  assign cy = din ^ 8'ha5;
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
endmodule

// 'o' is a port, but only a temporary of the block computing 'mix'
module sub_tmp (
    input logic [7:0] i,
    output logic [7:0] o,
    output logic [7:0] obs
);
  /*verilator no_inline_module*/
  logic [7:0] mix;
  logic [7:0] cpy;
  always_comb begin
    o = i ^ 8'h5a;
    mix = o + 8'd3;
  end
  always_comb cpy = o;
  assign obs = mix ^ cpy;
endmodule

interface ifc_din (
    input logic [7:0] din
);
  logic [7:0] a;
  assign a = din + 8'h11;
endinterface

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
module t (
    input logic clk,
    input logic rst,
    input logic rst_n,
    input logic set_n,
    input logic ld,
    input logic en,
    input logic never,
    input logic [1:0] sel,
    input logic [7:0] d,
    input logic [7:0] in_a,
    output logic [7:0] out_q,
    output logic [7:0] out_c,
    output logic [7:0] out_m
);

  typedef struct packed {
    logic [6:0] cnt;
    logic busy;
  } st_t;

  localparam logic [7:0] CST = 8'h3c;

  // Writable
  logic [7:0] ff_q;
  logic [7:0] arn_q;
  logic [7:0] arp_q;
  logic [7:0] as_q;
  logic [7:0] al_q;
  logic [7:0] lat_q;
  logic [7:0] ilat_q;
  logic [7:0] undr_mem[4];
  logic [7:0] init_r = 8'h11;
  logic [7:0] ini_r;
  logic [7:0] imp_l;

  always_ff @(posedge clk) ff_q <= d;
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) arn_q <= '0;
    else arn_q <= d;
  always_ff @(posedge clk or posedge rst)
    if (rst) arp_q <= '0;
    else arp_q <= d;
  always_ff @(posedge clk or negedge set_n)
    if (!set_n) as_q <= '1;
    else as_q <= d;
  always_ff @(posedge clk or posedge ld)
    if (ld) al_q <= in_a;
    else al_q <= d;
  always_latch if (en) lat_q = d;
  /* verilator lint_off LATCH */
  always @* if (en) ilat_q = d;
  /* verilator lint_on LATCH */
  initial ini_r = 8'h22;
  always_ff @(posedge clk) out_q <= d;

  // Read-only
  logic [7:0] asg_w;
  logic [7:0] ac_c;
  logic [7:0] star_c;
  logic [7:0] sub_o;
  logic [7:0] fc_c;
  logic gclk;
  logic [7:0] g_q;
  logic [7:0] vidx[4];
  logic [7:0] cst_w;
  logic [7:0] loop_c;
  logic [7:0] while_c;

  assign asg_w = d ^ 8'h0f;
  always_comb ac_c = d + 8'd1;
  always @* begin
    star_c = '0;
    if (en) star_c = d;
  end
  assign out_c = d & 8'hf0;
  sub u_sub (
      .i(d),
      .o(sub_o)
  );
  always @*
    case (sel)
      2'd0: fc_c = d;
      2'd1: fc_c = in_a;
      2'd2: fc_c = ~d;
      2'd3: fc_c = ~in_a;
    endcase
  // A latch, impure or not
  /* verilator lint_off LATCH */
  always @* begin
    if (en) imp_l = d;
    if (never) $display("%0d", imp_l);
  end
  /* verilator lint_on LATCH */
  assign gclk = clk & en;
  always_ff @(posedge gclk) g_q <= d;
  always_comb vidx[sel] = d;
  assign cst_w = CST;
  always_comb for (int i = 0; i < 200; i++) loop_c = d + 8'(i);
  always_comb begin
    int i;
    i = 0;
    while (i < 100) begin
      while_c = d;
      i++;
    end
  end

  // Writability must not depend on optimisation flags: V3Split parts the latch from the
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
  logic [7:0] vec;
  logic [7:0] pmem[4];

  always_ff @(posedge clk) st.cnt <= st.cnt + 7'd1;
  assign st.busy = st.cnt != '0;
  always_ff @(posedge clk) vec[7:1] <= d[7:1];
  assign vec[0] = en;
  assign pmem[1] = d;
  assign pmem[3] = ~d;

  always_ff @(posedge clk) out_m[7:1] <= d[7:1];
  assign out_m[0] = en;

  // A partial write past VPI_TABLE_MAX_DIMS can't build a per-bit mask, so the whole
  // variable is treated as comb-driven, even the element the write never touches.
  logic [1:0][3:0] m4[2][2];
  logic [7:0] m4_c;
  assign m4[0][0][0] = d[3:0];
  assign m4_c = {4'b0, m4[0][0][0]};

  // Ports: a child's output flop is writable, the parent's net on it and a child's input are not
  logic [7:0] w_ff;
  logic [7:0] w_mix;
  logic [7:0] pf;
  logic [7:0] in_o;
  logic [7:0] n_q;
  logic [7:0] n_ff;
  logic [7:0] n_mix;
  logic [7:0] n_if;
  logic [7:0] n_in;
  logic [7:0] n_cons;
  ifc bus ();
  // Nothing drives intf_inst.sig, so it is undriven storage
  ifc_cons intf_inst ();
  sub_cons u_cons (
      .clk,
      .bus(intf_inst),
      .cap(n_cons)
  );

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
  always_ff @(posedge clk) pf <= d;
  sub u_in (
      .i(pf),
      .o(in_o)
  );
  always_ff @(posedge clk) begin
    n_q <= out_q;
    n_ff <= w_ff;
    n_mix <= w_mix;
    n_if <= bus.q;
    n_in <= in_o;
  end

  // Instances of one variable driven differently from their parent: each is writable as
  // --public-flat-rw would persist a put into it, inlined or not
  logic [7:0] n_ia;
  logic [7:0] n_cf0;
  logic [7:0] n_cu;
  logic [7:0] n_mc2;
  ifc_pair ia ();
  ifc_pair ib ();
  always_ff @(posedge clk) ia.q <= d;
  assign ib.q = ia.q;
  sub_st cf0 ();
  sub_st cf1 ();
  sub_st cu ();
  sub_st cp ();
  always_ff @(posedge clk) cf0.p <= d;
  assign cf1.p = ~d;
  assign cp.p[3:0] = d[3:0];
  sub_ni mc0 ();
  sub_ni mc1 ();
  sub_ni mc2 ();
  assign mc0.m[3:0] = d[3:0];
  assign mc1.m[7:4] = in_a[7:4];
  always_ff @(posedge clk) mc2.m <= d;
  always_ff @(posedge clk) begin
    n_ia <= ia.q;
    n_cf0 <= cf0.p;
    n_cu <= cu.p;
    n_mc2 <= mc2.m;
  end

  // Comb shapes, each read-only: chained, signed, concatenated, self-reading, partial,
  // assembled from ranges or struct fields, left partly undriven, aggregate, multiply driven
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } hl_t;
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
  } us_t;
  logic [7:0] k_q, ch1, ch2, cat_c, self_c, part_c, ctv_c, nopre_c;
  logic signed [7:0] sgn_c;
  hl_t cts_c, hl_c;
  us_t us_c;
  logic [7:0] mem_c[2];
  logic [7:0] mdp_c[2][2];
  /* verilator lint_off MULTIDRIVEN */
  wire [7:0] mixf_w, ovl_w;
  /* verilator lint_on MULTIDRIVEN */
  always_ff @(posedge clk) k_q <= d;
  assign ch1 = k_q + 8'h7;
  assign ch2 = ch1 ^ 8'h2a;
  assign sgn_c = $signed(k_q) - 8'sd3;
  assign cat_c = {ch1[3:0], k_q[7:4]};
  always_comb begin
    self_c = k_q;
    self_c = self_c + 8'h1;
  end
  always_comb begin
    part_c = '0;
    part_c[3:0] = k_q[3:0];
  end
  assign ctv_c[3:0] = k_q[3:0];
  assign ctv_c[7:4] = in_a[3:0];
  assign cts_c.hi = k_q[3:0];
  assign cts_c.lo = in_a[3:0];
  always_comb nopre_c[3:0] = k_q[3:0];
  always_comb hl_c = d;
  always_comb us_c = '{d, ~d};
  always_comb mem_c = '{d, ~d};
  always_comb begin
    mdp_c[0][0] = d;
    mdp_c[0][1] = in_a;
    mdp_c[1] = '{~d, ~in_a};
  end
  assign mixf_w = k_q;
  assign mixf_w[2:0] = in_a[2:0];
  assign ovl_w[4:0] = k_q[4:0];
  assign ovl_w[7:2] = in_a[5:0];

  // Latches per bit: the bits some path through an if-tree leaves unassigned take a put
  logic [7:0] pla_l, plc_l, plf_l, plv_c, pli_l, plo_l;
  /* verilator lint_off MULTIDRIVEN */
  logic [7:0] plb_l;
  /* verilator lint_on MULTIDRIVEN */
  logic [7:0] plm_l[2];
  logic [7:0] ple_l[2];
  logic [7:0] plu_l[2];
  /* verilator lint_off LATCH */
  always @* if (en) pla_l[3:0] = d[3:0];
  always @* if (en) plb_l[3:0] = d[3:0];
  assign plb_l[7:4] = in_a[7:4];
  always @* begin
    if (en) plc_l[3:0] = d[3:0];
    plc_l[1:0] = in_a[1:0];
  end
  always @*
    if (en) plf_l = d;
    else plf_l[3:0] = in_a[3:0];
  always @* if (en) plv_c[{1'b0, sel}] = d[0];
  always @* begin
    if (en) plm_l[0] = d;
    plm_l[1] = in_a;
  end
  always @* begin
    if (en) ple_l[1][7:4] = d[7:4];
    ple_l[1][3:0] = in_a[3:0];
  end
  always @* begin
    pli_l[1:0] = d[1:0];
    if (en) begin
      pli_l[3:2] = d[3:2];
      pli_l[5:4] = '0;
    end else if (sel[0]) pli_l[5:2] = in_a[5:2];
    else if (ON) begin
      pli_l[4:2] = '0;
      pli_l[5] = 1'b1;
    end else pli_l[7:6] = '0;
  end
  always @*
    if (1'b0) plo_l[7:6] = d[7:6];
    else if (en) plo_l[5:0] = d[5:0];
    else plo_l[7:2] = in_a[7:2];
  always @*
    if (en) begin
      plu_l[0] = d;
      plu_l[1][3:0] = d[3:0];
    end else begin
      plu_l[1] = in_a;
      plu_l[0][7:4] = in_a[7:4];
    end
  /* verilator lint_on LATCH */

  // Copy and fold rows: aliases of a flop, a pass-through port, a copy of a cone and two
  // siblings of one; then a net driven through a port and directly, a public_flat_rd a cone
  // reads, and a write at an impure index
  logic [7:0] al1, al2, pass_o, fold_c, fmid_c, sib_b, sib_c, rdpin_c, ivec;
  logic [7:0] rdpin  /*verilator public_flat_rd*/;
  logic [31:0] seedv;
  wire [7:0] wd_w;
  assign al1 = k_q;
  assign al2 = al1;
  sub_pass u_pass (
      .i(k_q),
      .o(pass_o)
  );
  always_comb fold_c = d ^ 8'h3c;
  always_comb fmid_c = fold_c;
  assign sib_b = ch1;
  assign sib_c = ch1;
  sub_pass u_wdrv (
      .i(in_a),
      .o(wd_w)
  );
  assign wd_w = d;
  always_ff @(posedge clk) rdpin <= d ^ 8'h6d;
  assign rdpin_c = rdpin ^ 8'h11;
  always_comb ivec[($urandom(seedv)&3)+:4] = d[3:0];

  // Aliases whose rows carry their own range, sign, net or bit type and packed dimensions
  logic signed [8:1] al_sw;
  wire [7:0] al_nw;
  bit [7:0] sib_bt;
  logic [1:0][7:0] pk_c, pk_al;
  assign al_sw = k_q;
  assign al_nw = k_q;
  assign sib_bt = ch1;
  assign pk_c = {ch1, k_q};
  assign pk_al = pk_c;
  sub_na u_na (
      .y(),
      .z(),
      .w(),
      .q(),
      .a(d)
  );

  // Instances of one class, its input a cone in one and a flop in the other; a submodule's
  // temporary copied out; an interface member; a comb cycle closed through two instances
  logic [7:0] tmp_o, tmp_obs, alc_x, alc_y;
  sub_cy cy0 (.din(d ^ in_a));
  sub_cy cy1 (.din(k_q));
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
  sub_tmp u_tmp (
      .i(d),
      .o(tmp_o),
      .obs(tmp_obs)
  );
  ifc_din ifd (.din(d));
  sub_pass u_lp1 (
      .i(alc_x),
      .o(alc_y)
  );
  sub_pass u_lp2 (
      .i(alc_y | 8'h0a),
      .o(alc_x)
  );

  // Statement shapes a cone refuses or prunes: a read before its write, by a statement, an if
  // and a loop test; a break out of a loop; a dead store, alone or in a loop; an unpacked struct
  // member lvalue; an impure continuous assign
  /* verilator lint_off UNOPTFLAT */
  logic [7:0] rbw_t, rbw_c, ifc_c, lt_lim, lt_c, brk_c, dpf_c, dlp_c, dus_c;
  logic ifc_t;
  /* verilator lint_on UNOPTFLAT */
  logic [7:0] dpf_t  /*verilator public_flat_rw*/;
  logic [7:0] dlp_t  /*verilator public_flat_rw*/;
  logic [31:0] rnd_w;
  us_t dus;
  /* verilator lint_off ALWCOMBORDER */
  always_comb begin
    rbw_c = rbw_t;
    rbw_t = d | in_a;
  end
  always_comb begin
    ifc_c = d;
    if (ifc_t) ifc_c = in_a;
    ifc_t = sel[1];
  end
  always_comb begin
    lt_c = 8'h0;
    for (int i = 0; i < int'(lt_lim); ++i) lt_c = lt_c + 8'h1;
    lt_lim = {6'b0, sel};
  end
  /* verilator lint_on ALWCOMBORDER */
  always_comb begin
    brk_c = 8'h0;
    for (int i = 0; i < int'(sel); ++i) begin
      if (d[0]) break;
      brk_c = brk_c + in_a;
    end
  end
  always_comb begin
    dpf_c = d + 8'h9;
    dpf_t = dpf_c ^ 8'h5;
  end
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
  logic [7:0] ret_c, ret_q;
  always_comb ret_c = k_q ^ 8'(8'h5a * $c(1));
  always_ff @(posedge clk) ret_q <= ret_c;

  // Runs once per eval for its input, and once more when the settle region re-runs
  logic [7:0] stl_c;
  always_comb begin
    $c("extern int settleRuns; settleRuns += 1 + 0 * ", in_a, ";");
    stl_c = in_a;
  end

  // A cone read twice from one eval, its input moved between the reads
  logic [7:0] mid_s, mid_c;
  assign mid_c = mid_s + 8'h1;
  initial begin
    mid_s = 8'h10;
    $c("extern void midEvalRead(int); midEvalRead(", mid_s, ");");
    mid_s = 8'h20;
    $c("extern void midEvalRead(int); midEvalRead(", mid_s, ");");
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

  // Explicitly writable
  logic [7:0] frw_c  /*verilator public_flat_rw*/;
  logic [7:0] frc_al  /*verilator forceable*/;
  assign frw_c = d;
  assign frc_al = in_a;

endmodule
