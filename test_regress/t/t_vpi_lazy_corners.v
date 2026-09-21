// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// --vpi-lazy bail/retain corners: constructs that must fall back to retained VPI storage.
module t (
  input  logic         clk,
  input  logic         rst,
  input  logic [7:0]   a,
  input  logic [7:0]   b,
  input  logic [2:0]   sel,
  input  logic         frc2_force,
  input  logic [3:0]   data,
  output logic [7:0]   out,
  output logic [7:0]   obs_dtypes,
  output logic [7:0]   observe_dimcap,
  output logic [6:0]   obs_chandle,
  output logic [7:0]   o_floor,
  output logic [7:0]   o_multidriven,
  output logic [6:0]   observe_forceable,
  output logic [7:0]   obs_impureidx,
  output logic [255:0] obus,
  output logic [255:0] obus2
);

  // impureidx: impure bit-select index cannot be re-evaluated, so must be retained
  logic [31:0] seedv;
  logic [7:0]  vec;
  always_comb vec[($urandom(seedv) & 3) +: 4] = data;
  assign obs_impureidx = vec;

  // iopartial: an IO port assembled from bit-slice writes is never reconstructable
  logic [7:0] keep;
  assign out[3:0] = keep[3:0];
  assign out[7:4] = keep[7:4] ^ 4'hf;
  always_ff @(posedge clk) begin
    if (rst) keep <= 8'h0;
    else keep <= keep + 8'h11;
  end

  // dtypes: basic and aggregate dtypes reconstruct
  typedef enum logic [1:0] { A, B, C, D } e_t;
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;
  typedef struct { logic [7:0] a; logic [7:0] b; } us_t;

  real    r_comb;    always_comb r_comb = 1.5;
  integer i_comb;    always_comb i_comb = a + 1;
  e_t     en_comb;   always_comb en_comb = e_t'(a[1:0]);
  string  s_var;     always_comb s_var = "hi";
  logic [6:0] v_comb; always_comb v_comb = a[6:0] ^ 7'h5;

  string  s_fmt;     always_comb s_fmt = $sformatf("v%0d", a);  // impure, group bails

  ps_t    ps_comb;   always_comb begin ps_comb.hi = a[7:4]; ps_comb.lo = a[3:0]; end
  logic [3:0][7:0] pa_comb;
  always_comb pa_comb = {a, a ^ 8'hff, a + 8'd1, a - 8'd1};

  us_t    us_comb;   always_comb begin us_comb.a = a; us_comb.b = ~a; end
  logic [7:0] mem [0:3];
  always_comb begin mem[0]=a; mem[1]=a+1; mem[2]=a+2; mem[3]=a+3; end

  // partialmem: only element 0 is written, so nothing proves the rest, and the array must keep
  // its storage rather than have a cone invent a zero for every undriven element
  logic [7:0] mem_part [0:3];
  always_comb mem_part[0] = a ^ 8'h27;

  // mdcover: the element-coverage proof over unequal, mixed-direction, non-zero-based dims,
  // with one element assembled from two adjacent packed slices. Every element is covered, so
  // the array reconstructs and VPI must read each one back.
  logic [15:0] md_full [3:1][0:1];
  always_comb begin
    md_full[1][0][7:0]  = a;
    md_full[1][0][15:8] = ~a;
    md_full[1][1] = {a, 8'h11};
    md_full[2][0] = {a, 8'h22};
    md_full[2][1] = {a, 8'h33};
    md_full[3][0] = {a, 8'h44};
    md_full[3][1] = {a, 8'h55};
  end

  // ... and the same shape with one element's high byte left undriven. Adjacency alone would
  // call that covered; the array must keep its storage rather than have a seeded zero invent a
  // value for bits nothing in the design assigns.
  logic [15:0] md_gap [0:1][2:0];
  always_comb begin
    md_gap[0][0][7:0] = a;
    md_gap[0][1] = {a, 8'h11};
    md_gap[0][2] = {a, 8'h22};
    md_gap[1][0] = {a, 8'h33};
    md_gap[1][1] = {a, 8'h44};
    md_gap[1][2] = {a, 8'h55};
  end

  assign obs_dtypes = v_comb ^ i_comb[7:0] ^ mem[0] ^ ps_comb ^ pa_comb[0] ^ us_comb.a
                     ^ {6'b0, en_comb} ^ {7'b0, s_fmt.len() != 0};

  // dimcap: 'wide' has one packed dim more than the VPI table's dv[] cap, so must retain
  logic [7:0] ctr;
  logic [1:0][1:0][1:0][1:0] wide;
  logic [7:0] narrow;

  assign wide = {ctr, ~ctr};
  assign narrow = ctr + 8'h1;

  always_ff @(posedge clk) begin
    if (rst) begin
      ctr <= 8'h0;
      observe_dimcap <= 8'h0;
    end else begin
      ctr <= ctr + 8'h3;
      observe_dimcap <= narrow;
    end
  end

  // chandle: opaque write-only signal, not reconstructable
  logic [6:0] cnt;
  chandle handle;
  always_ff @(posedge clk) begin
    if (rst) begin
      cnt <= 7'h0;
      handle <= null;
    end else begin
      cnt <= cnt + 7'h1;
    end
  end
  assign obs_chandle = cnt;

  // floor: completeness floor retains undriven residuals; split_var is refused here
  logic [7:0] recon;
  assign recon = a + 8'd1;

  logic [7:0] orphan;  // undriven/unread: floor retains, plain lazy drops

  logic [7:0] p /*verilator split_var*/;
  assign p[3:0] = a[3:0];
  always_comb p[7:4] = a[7:4];

  assign o_floor = recon;

  // multidriven: 'w' retained; 'r' reconstructed
  logic [7:0] w;
  assign w = a;
  assign w = b;

  logic [7:0] r;
  assign r = a & b;

  assign o_multidriven = w ^ r;

  // forceable: forceable signals are excluded from lazy reconstruction
  logic [6:0] keep_frc;
  logic [6:0] frc  /* verilator forceable */;
  logic [6:0] frc2;

  assign frc = keep_frc + 7'h11;
  assign frc2 = keep_frc + 7'h22;

  always_ff @(posedge clk) begin
    if (rst) begin
      keep_frc <= 7'h0;
      observe_forceable <= 7'h0;
    end else begin
      keep_frc <= keep_frc + 7'h3;
      observe_forceable <= frc;
    end
  end

  // frc2 has no forceable metacomment but is forced by SV force/release, so it must still
  // be marked isForceable() under --vpi-lazy
  always @(posedge clk) begin
    if (frc2_force) force frc2 = 7'h55;
    else release frc2;
  end

  // foldcorners: compile-only cover of the group classifier's reconstruct/retain branches
  logic [7:0] troot, lz_root;
  always_comb begin
    troot = a & b;
    lz_root = troot;
  end

  logic [7:0] ttp, lz_tp;
  always_comb begin
    ttp = a;
    ttp[3:0] = b[3:0];
    lz_tp = ttp;
  end

  logic [7:0] tpf, lz_pf;
  always_comb begin
    tpf[3:0] = a[3:0];
    lz_pf = tpf;
  end

  logic [7:0] uarr [0:1];
  logic [7:0] lz_nv;
  always_comb begin
    uarr[0] = a;
    lz_nv = uarr[0] ^ b;
  end

  logic [7:0] ttb, lz_tb;
  always_comb begin
    ttb = 8'h0;
    if (sel[0]) ttb = a;
    lz_tb = ttb + b;
  end

  logic [7:0] trbw, lz_rbw;
  always_comb begin
    lz_rbw = trbw;
    trbw = a | b;
  end

  logic [7:0] lz_ifc;
  logic tc;
  always_comb begin
    lz_ifc = a;
    if (tc) lz_ifc = b;
    tc = sel[1];
  end

  // Impure RHS bails the group
  logic [7:0] lz_imp;
  always_comb lz_imp = a + $c8("0");

  logic [7:0] mixp;
  assign mixp[3:0] = a[3:0];
  always_comb mixp[7:4] = b[3:0];

  // Multi-driven comb, retained
  logic [7:0] two;
  always_comb two = a;
  always_comb two = b;

  logic [7:0] disj;
  assign disj[3:0] = a[3:0];
  assign disj[7:4] = b[3:0];

  assign obus = {lz_root, lz_tp, lz_pf, lz_nv, lz_tb, lz_rbw, lz_ifc,
                 lz_imp, mixp, two, disj, {21{8'h0}}};

  // walkcorners: statement shapes the ordered walk models, and the ones it refuses.
  // A non-constant bound keeps the loop out of V3Unroll's reach, so AstLoop/AstLoopTest
  // still exist when V3VpiLazy runs.
  logic [7:0] lz_loop;
  always_comb begin
    lz_loop = 8'h0;
    for (int i = 0; i < int'(sel); ++i) lz_loop = lz_loop + a;
  end

  // A `break` wraps the loop in an AstJumpBlock
  logic [7:0] lz_brk;
  always_comb begin
    lz_brk = 8'h0;
    for (int i = 0; i < int'(sel); ++i) begin
      if (a[0]) break;
      lz_brk = lz_brk + b;
    end
  end

  // A loop test reading a group member before its write bails read-before-write
  logic [7:0] lz_ltrbw, ltlim;
  always_comb begin
    lz_ltrbw = 8'h0;
    for (int i = 0; i < int'(ltlim); ++i) lz_ltrbw = lz_ltrbw + 8'h1;
    ltlim = {5'b0, sel};
  end

  // V3Active rewrites a comb-block '<=' to '=' but keeps the delay, which a cold
  // reconstruction must not re-execute
  logic [7:0] lz_nbd;
  // verilator lint_off COMBDLY
  always_comb lz_nbd <= #1 a;
  // verilator lint_on COMBDLY

  // An unpacked struct member write has no single base VarRef for the walk to follow.
  // Every dead-store block below depends on its target so V3Split keeps it whole.
  us_t dead_us;
  logic [7:0] lz_us;
  always_comb begin
    lz_us = a + 8'h6;
    dead_us.a = lz_us;
    dead_us.b = ~lz_us;
  end

  // Element-written array seeding: overlapping writes, and mixed select depth
  logic [7:0] ovl [0:1];
  logic [7:0] lz_ovl;
  always_comb begin
    ovl[0] = a;
    ovl[0] = b;
    ovl[1] = a ^ b;
    lz_ovl = a + b;
  end

  logic [7:0] mdep [0:1][0:1];
  logic [7:0] lz_mdep;
  always_comb begin
    mdep[0][0] = a;
    mdep[1] = '{8'h1, 8'h2};
    lz_mdep = a - b;
  end

  // Continuous partial writes of one array at differing select depth cannot be assembled
  logic [7:0] pdep [0:1][0:1];
  assign pdep[0] = '{8'h11, 8'h22};
  assign pdep[1][0] = a;
  assign pdep[1][1] = b;

  // A public_flat_rw signal keeps its own storage, so under --vpi-lazy it is a group temp,
  // not a target. Read from a second cone, its shadow is referenced from two reconstruct
  // functions and so cannot be localized.
  logic [7:0] shared_t /*verilator public_flat_rw*/;
  logic [7:0] lz_sa, lz_sb;
  always_comb begin
    shared_t = a + 8'h7;
    lz_sa = shared_t ^ 8'h1;
  end
  always_comb lz_sb = shared_t | 8'h2;

  // An unread temp store is dead in the reconstruction, so the liveness prune drops it
  logic [7:0] dead_pf /*verilator public_flat_rw*/;
  logic [7:0] lz_dead;
  always_comb begin
    lz_dead = a + 8'h9;
    dead_pf = lz_dead ^ 8'h5;
  end

  // ... and a jump block whose whole body prunes away goes with it
  logic [7:0] dead_lp /*verilator public_flat_rw*/;
  logic [7:0] lz_deadlp;
  always_comb begin
    lz_deadlp = a ^ 8'h3;
    for (int i = 0; i < int'(sel); ++i) begin
      if (a[1]) break;
      dead_lp = lz_deadlp + 8'h1;
    end
  end


  // An explicit public_flat_rd read by a cone stays read-only, pinned but not writable
  logic [7:0] rdpin /*verilator public_flat_rd*/;
  logic [7:0] lz_rdpin;
  always_ff @(posedge clk) rdpin <= a ^ 8'h6d;
  always_comb lz_rdpin = rdpin ^ 8'h11;

  // copyalias: a pure alias of a flop, which keeps its storage, so the alias needs no cone -
  // its descriptor copies that storage on read
  logic [7:0] cpy_src;
  logic [7:0] cpy_alias;
  always_ff @(posedge clk) cpy_src <= a + 8'h21;
  assign cpy_alias = cpy_src;

  // foldcopy: a one-statement comb copy of another cone needs no func of its own - its
  // descriptor calls that cone's func and copies its shadow
  logic [7:0] fold_src;
  logic [7:0] fold_mid;
  always_comb fold_src = a ^ 8'h3c;
  always_comb fold_mid = fold_src;

  // realcopy: real and string rows have no memcpy width, so a copy or fold source must leave
  // them cones - a descriptor would refresh zero bytes, and a std::string cannot be raw-copied
  real   rc_src;
  real   rc_alias;
  string sc_src;
  string sc_alias;
  always_ff @(posedge clk) begin
    rc_src <= $itor(a) + 0.5;
    sc_src <= a[0] ? "odd" : "even";
  end
  always_comb rc_alias = rc_src;
  always_comb sc_alias = sc_src;

  real   rf_mid;
  string sf_mid;
  always_comb rf_mid = r_comb;
  always_comb sf_mid = s_var;

  // sibalias: two aliases of one reconstructed canonical. Each needs storage of its own, or a
  // deposit into one is seen through the other and through the canonical (PR 7945 review case).
  logic [7:0] sib_canon;
  logic [7:0] sib_b;
  logic [7:0] sib_c;
  always_comb sib_canon = a ^ 8'h5a;
  assign sib_b = sib_canon;
  assign sib_c = sib_canon;

  assign obus2 = {lz_loop, lz_brk, lz_ltrbw, lz_nbd, lz_us, lz_ovl, lz_mdep,
                  pdep[0][0], pdep[1][1], lz_sa, lz_sb, lz_dead, lz_deadlp,
                  ovl[0], ovl[1], mdep[0][0], mdep[1][0], dead_us.a, lz_rdpin,
                  cpy_alias, fold_mid, sib_b, sib_c, {9{8'h0}}};

endmodule
