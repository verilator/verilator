// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Automatic splitting of unpacked arrays and structs
// Variables expected to be split are marked with a 'Split N' comment, where N is the
// number of variables split: the variable itself, and its components split further.

typedef struct {
  logic [6:0] a;
  logic [32:0] b;
  logic [4:0] c [2:3];
} st_t;

typedef struct {
  logic [4:0] m [4];
} sm_t;

typedef struct {
  logic [6:0] x [4];
  logic [6:0] y [4];
} sxy_t;

typedef struct {
  logic [6:0] d;
  logic k;  // Declared last, so the first component
} sk_t;

typedef struct {
  logic [6:0] v [4];
  logic i;  // Declared last, so the first component
} suv_t;

typedef union {
  logic [6:0] x;
  logic [6:0] y;
} uu_t;

typedef struct {
  uu_t u;
  logic [6:0] d;
} su_t;

typedef struct packed {
  logic [3:0] x;
  logic [3:0] y;
} pst_t;

class Cls;
  int val;
endclass

module t (
    input clk
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;
  logic [63:0] crc_q = '0;

  // Descending, non-zero based, written in an unrolled loop
  logic [6:0] dn [3:1];  // Split 1
  // Ascending, non-zero based
  logic [14:0] up [2:4];  // Split 1
  // Multi-dimensional with different ranges
  logic [4:0] md [0:2][3:1];  // Split 4
  // Whole array copies, same and opposite direction
  logic [6:0] cp [3:1];  // Split 1
  logic [6:0] rev [1:3];  // Split 1
  // Whole array copy, opposite direction, more elements than the slice limit
  logic [6:0] revd [3:0];  // No split: opposite direction
  // Assignment patterns
  logic [7:0] pat [0:3];  // No split: pattern value
  logic [7:0] pat_lo;
  logic [7:0] pat_hi;
  logic [32:0] def [2:0];  // Split 1
  // Chain through elements, would be UNOPTFLAT if not split
  logic [6:0] chain [0:3];  // Split 1
  // Unpacked structs, whole copy
  st_t st;  // Split 2
  st_t st_cp;  // Split 2
  // Other element types
  real rl [1:0];  // Split 1
  string str [0:1];  // Split 1
  // Non-blocking assignment in an unrolled loop
  logic [6:0] q [3:1];  // Split 1
  // Variable index
  logic [6:0] dyn [4];  // No split: variable index
  // Array of unpacked structs
  st_t sa [2][2];  // Split 11
  // Whole copy into an array that is not split
  logic [4:0] mdp [0:2][3:1]  /*verilator public*/;  // No split: public
  // Whole copy of a struct element
  st_t sar;  // Split 2
  // Selected with variable indices, and assigned to and from them
  logic sel;
  logic nsel;
  st_t sv [2];  // No split: variable index
  st_t sv2 [2];  // No split: variable index
  // Forced, and assigned from it
  logic [6:0] frc [2];  // No split: forced
  logic [6:0] frcr [2];  // No split: assigned from a forced variable
  // Struct pattern reading the variable itself
  st_t ssw = '{a: 7'd1, b: 33'd2, c: '{5'd3, 5'd4}};  // No split: pattern value
  // Struct selected with a cheap index expression, and assigned from it
  st_t sx [2];  // No split: index expression
  st_t sxr;  // Split 1
  // Struct copied to an element selected with an index expression
  st_t sz;  // No split: copied to a select with an index expression
  st_t szz [2];  // No split: index expression
  // Assigned from a member of an element selected with a variable index, more elements than the
  // slice limit
  sm_t smv [2];  // No split: variable index
  logic [4:0] cs [4];  // Split 1
  // Assigned from an element selected with a narrow index, more elements than the slice limit
  logic [6:0] t8 [8][4];  // No split: variable index
  logic [6:0] ce [4];  // Split 1
  // Copied to elements selected with indices reading the variable itself
  st_t sref;  // Split 2
  st_t srefs [2];  // No split: index expression
  // Member copied from another member of the same variable
  sxy_t sab;  // Split 3
  // Copied to an element selected with an index reading the element's own variable
  sk_t skb;  // Split 1
  sk_t ska [2];  // No split: index expression
  // Same, with a non-blocking assignment, checked against a reference model
  sk_t skd;  // Split 1
  sk_t skad [2];  // No split: index expression
  logic [7:0] skr [2];
  // Assigned from an element selected with an index reading its own member, assigned to a
  // temporary first
  suv_t uq;  // Split 2
  suv_t utab [2];  // No split: variable index
  logic ui;
  // Struct with an unpacked union member, which is not split
  su_t su;  // Split 1
  // Packed struct
  pst_t pk;
  // Function result
  logic [6:0] fxo;
  // Result from an automatic local, reset on entry
  logic [6:0] locx;
  // Interface array accessed via a virtual interface
  ifc u_ifc ();
  virtual ifc vi = u_ifc;
  // Other element types: events, class handles, virtual interfaces, queues
  event ev [2];  // Split 1
  int evcnt0 = 0;
  int evcnt1 = 0;
  Cls objs [2];  // Split 1
  ifc u_ifc2 ();
  virtual ifc vis [2];  // Split 1
  int qs [2][$];  // Split 1
  // Connected to unpacked ports of a module that is not inlined
  logic [6:0] pin [2];  // Split 1
  logic [6:0] pout [2];  // Split 1
  // Only copied whole, so not split
  logic [6:0] cw1 [4];  // No split: only copied whole
  logic [6:0] cw2 [4];  // No split: only copied whole
  logic [6:0] cwo [4];  // No split: variable index
  // Only copied whole, but copied to a variable that is split, so split too
  logic [6:0] cl1 [4];  // Split 1
  logic [6:0] cl2 [4];  // Split 1
  // Chain of whole copies, only the last selected from, so split from the end of the chain
  logic [6:0] wc0 [4];  // Split 1
  logic [6:0] wc1 [4];  // Split 1
  logic [6:0] wc2 [4];  // Split 1
  logic [6:0] wc3 [4];  // Split 1

  always_comb begin
    for (int i = 1; i <= 3; i++) dn[i] = crc[i*7+:7];
    for (int i = 2; i <= 4; i++) up[i] = crc[i*15-30+:15];
    for (int i = 0; i <= 2; i++) begin
      for (int j = 1; j <= 3; j++) md[i][j] = crc[i*15+j*5-5+:5];
    end
  end

  assign cp = dn;
  always_comb rev = dn;
  assign revd = dyn;

  // Registered, so the pattern elements are of the element type
  always_ff @(posedge clk) pat_lo <= crc[7:0];
  always_ff @(posedge clk) pat_hi <= crc[15:8];
  always_comb pat = '{8'h11, pat_lo, pat_hi, 8'h44};
  always_comb def = '{default: crc[40:8]};

  assign chain[0] = crc[6:0];
  for (genvar g = 1; g < 4; g++) begin : gen_chain
    assign chain[g] = chain[g-1] + 7'd1;
  end

  always_comb begin
    st.a = crc[6:0];
    st.b = crc[40:8];
    st.c[2] = crc[45:41];
    st.c[3] = crc[50:46];
  end
  assign st_cp = st;

  always_comb begin
    rl[0] = real'(crc[7:0]);
    rl[1] = real'(crc[15:8]) / 2.0;
    str[0] = crc[0] ? "one" : "zero";
    str[1] = "fixed";
  end

  always_ff @(posedge clk) begin
    for (int i = 1; i <= 3; i++) q[i] <= dn[i];
    crc_q <= crc;
  end

  always_comb begin
    for (int i = 0; i < 4; i++) dyn[i] = crc[i*7+:7];
  end

  always_comb begin
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 2; j++) begin
        sa[i][j].a = crc[i*7+j+:7];
        sa[i][j].b = crc[i+j+:33];
        sa[i][j].c[2] = crc[i*5+j+:5];
        sa[i][j].c[3] = crc[i*5+j+10+:5];
      end
    end
  end

  always_comb begin
    mdp = md;
    sar = sa[1][0];
  end

  assign sel = crc[0];
  assign nsel = ~crc[0];
  always_comb begin
    sv[sel].a = crc[6:0];
    sv[sel].b = crc[40:8];
    sv[sel].c[2] = crc[4:0];
    sv[sel].c[3] = crc[9:5];
    sv[nsel] = st;
    sv2[sel] = sv[nsel];
    sv2[nsel] = sv[sel];
  end

  always_comb frc = '{crc[6:0], crc[13:7]};
  initial force frc[1] = 7'h55;
  always_comb frcr = frc;

  always_ff @(posedge clk) ssw <= '{a: ssw.b[6:0], b: 33'(ssw.a), c: ssw.c};

  always_comb begin
    sx[0] = st;
    sx[1] = st_cp;
    sxr = sx[crc[0]];
  end

  always_comb begin
    sz.a = crc[6:0];
    sz.b = crc[40:8];
    sz.c[2] = crc[4:0];
    sz.c[3] = crc[9:5];
    szz[crc[0]] = sz;
    szz[~crc[0]] = sz;
  end

  always_comb pk = crc[7:0];

  always_comb begin
    su.u.x = crc[6:0];
    su.d = crc[13:7];
  end

  always_comb begin
    for (int i = 0; i < 4; i++) begin
      smv[sel].m[i] = crc[i*5+:5];
      smv[nsel].m[i] = crc[i*5+20+:5];
    end
    cs = smv[sel].m;
  end

  always_comb begin
    for (int i = 0; i < 8; i++) begin
      for (int j = 0; j < 4; j++) t8[i][j] = crc[i*7+j+:7];
    end
    ce = t8[3'(crc[1:0])];
  end

  always_comb begin
    sref.a = crc[6:0];
    sref.b = crc[40:8];
    sref.c[2] = {4'b0, crc[0]};
    sref.c[3] = {4'b0, ~crc[0]};
    srefs[sref.c[2][0]] = sref;
    srefs[sref.c[3][0]] = sref;
  end

  always_comb begin
    for (int i = 0; i < 4; i++) sab.y[i] = crc[i*7+:7];
    sab.x = sab.y;
  end

  always_comb begin
    skb.d = crc[6:0];
    skb.k = crc[7];
    ska[0] = '{d: 7'h55, k: 1'b0};
    ska[1] = '{d: 7'h2a, k: 1'b0};
    ska[ska[0].k] = skb;
  end

  always_comb begin
    skd.d = crc[13:7];
    skd.k = crc[14];
  end

  always @(posedge clk) begin
    if (cyc == 0) begin
      skad[0] <= '{d: 7'h55, k: 1'b0};
      skad[1] <= '{d: 7'h2a, k: 1'b0};
      skr[0] <= {7'h55, 1'b0};
      skr[1] <= {7'h2a, 1'b0};
    end else begin
      skad[skad[0].k] <= skd;
      skr[skr[0][0]] <= {skd.d, skd.k};
      `checkh(skad[0].d, skr[0][7:1]);
      `checkh(skad[0].k, skr[0][0]);
      `checkh(skad[1].d, skr[1][7:1]);
      `checkh(skad[1].k, skr[1][0]);
    end
  end

  always @(posedge clk) begin
    if (cyc == 0) begin
      utab[0] = '{v: '{7'h11, 7'h12, 7'h13, 7'h14}, i: 1'b1};
      utab[1] = '{v: '{7'h21, 7'h22, 7'h23, 7'h24}, i: 1'b0};
      for (int k = 0; k < 4; k++) uq.v[k] = 7'(k);
      uq.i = 1'b0;
    end else begin
      ui = uq.i;
      uq = utab[uq.i];
      `checkh(uq.i, utab[ui].i);
      `checkh(uq.v[0], utab[ui].v[0]);
      `checkh(uq.v[3], utab[ui].v[3]);
    end
  end

  assign cw1 = dyn;
  assign cw2 = cw1;
  assign cwo = cw2;
  assign cl1 = dyn;
  assign cl2 = cl1;
  assign wc0 = dyn;
  assign wc1 = wc0;
  assign wc2 = wc1;
  assign wc3 = wc2;

  function automatic logic [6:0] fx(input logic [6:0] v);
    logic [6:0] tmp [2];  // Split 1
    tmp[0] = v;
    tmp[1] = ~v;
    return tmp[0] ^ tmp[1];
  endfunction
  assign fxo = fx(crc[6:0]);

  always_comb begin
    automatic logic [6:0] loc [2];  // Split 1
    loc[0] = crc[6:0];
    loc[1] = crc[13:7];
    locx = loc[0] ^ loc[1];
  end

  always_comb begin
    u_ifc.arr[0] = crc[6:0];
    u_ifc.arr[1] = crc[13:7];
  end
  always @(posedge clk) begin
    ->ev[0];
    if (cyc[0]) ->ev[1];
  end
  always @(ev[0]) evcnt0 <= evcnt0 + 1;
  always @(ev[1]) evcnt1 <= evcnt1 + 1;

  initial begin
    objs[0] = new;
    objs[1] = new;
    vis[0] = u_ifc;
    vis[1] = u_ifc2;
  end

  always_comb begin
    u_ifc2.arr[0] = crc[20:14];
    u_ifc2.arr[1] = crc[27:21];
  end

  always_comb begin
    pin[0] = crc[6:0];
    pin[1] = crc[13:7];
  end
  psub u_psub (
      .pin(pin),
      .pout(pout)
  );

  sub u_sub0 (
      .clk(clk),
      .crc(crc)
  );
  sub u_sub1 (
      .clk(clk),
      .crc(~crc)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    `checkh(dn[1], crc[13:7]);
    `checkh(dn[2], crc[20:14]);
    `checkh(dn[3], crc[27:21]);
    `checkh(up[2], crc[14:0]);
    `checkh(up[3], crc[29:15]);
    `checkh(up[4], crc[44:30]);
    `checkh(md[0][1], crc[4:0]);
    `checkh(md[1][2], crc[24:20]);
    `checkh(md[2][3], crc[44:40]);
    `checkh(cp[1], dn[1]);
    `checkh(cp[3], dn[3]);
    `checkh(rev[1], dn[3]);
    `checkh(rev[2], dn[2]);
    `checkh(rev[3], dn[1]);
    // Broken: whole array copy of opposite direction, not sliced, copies slot by slot
    // `checkh(revd[3], dyn[0]);
    // `checkh(revd[1], dyn[2]);
    // `checkh(revd[0], dyn[3]);
    `checkh(pat[0], 8'h11);
    `checkh(pat[1], pat_lo);
    `checkh(pat[2], pat_hi);
    `checkh(pat[3], 8'h44);
    `checkh(def[0], crc[40:8]);
    `checkh(def[2], crc[40:8]);
    `checkh(chain[3], crc[6:0] + 7'd3);
    `checkh(st.a, crc[6:0]);
    `checkh(st.b, crc[40:8]);
    `checkh(st.c[2], crc[45:41]);
    `checkh(st.c[3], crc[50:46]);
    `checkh(st_cp.a, st.a);
    `checkh(st_cp.b, st.b);
    `checkh(st_cp.c[2], st.c[2]);
    `checkh(st_cp.c[3], st.c[3]);
    `checkh(rl[0] == real'(crc[7:0]), 1'b1);
    `checkh(rl[1] == real'(crc[15:8]) / 2.0, 1'b1);
    `checks(str[0], crc[0] ? "one" : "zero");
    `checks(str[1], "fixed");
    `checkh(dyn[crc[1:0]], crc[crc[1:0]*7+:7]);
    `checkh(sa[1][1].a, crc[14:8]);
    `checkh(sa[1][1].b, crc[34:2]);
    `checkh(sa[1][1].c[2], crc[10:6]);
    `checkh(sa[1][1].c[3], crc[20:16]);
    `checkh(mdp[2][3], md[2][3]);
    `checkh(sar.b, crc[33:1]);
    `checkh(sar.c[3], crc[19:15]);
    `checkh(sv[sel].a, crc[6:0]);
    `checkh(sv[sel].c[3], crc[9:5]);
    `checkh(sv[nsel].b, st.b);
    `checkh(sv2[sel].b, st.b);
    `checkh(sv2[nsel].c[3], crc[9:5]);
    `checkh(frcr[0], crc[6:0]);
    `checkh(frcr[1], 7'h55);
    `checkh(ssw.a ^ ssw.b[6:0], 7'd3);
    `checkh(ssw.c[2], 5'd3);
    `checkh(sxr.b, crc[0] ? st_cp.b : st.b);
    `checkh(szz[0].a, crc[6:0]);
    `checkh(szz[1].c[3], crc[9:5]);
    `checkh(pk.y, crc[3:0]);
    `checkh(su.u.y, crc[6:0]);
    `checkh(su.d, crc[13:7]);
    `checkh(cs[0], crc[4:0]);
    `checkh(cs[3], crc[19:15]);
    `checkh(ce[1], crc[crc[1:0]*7+1+:7]);
    `checkh(ce[3], crc[crc[1:0]*7+3+:7]);
    `checkh(srefs[crc[0]].a, crc[6:0]);
    `checkh(srefs[1].b, crc[40:8]);
    `checkh(srefs[~crc[0]].c[3], {4'b0, ~crc[0]});
    `checkh(sab.x[0], crc[6:0]);
    `checkh(sab.x[3], crc[27:21]);
    `checkh(ska[0].d, crc[6:0]);
    `checkh(ska[0].k, crc[7]);
    `checkh(ska[1].d, 7'h2a);
    `checkh(cwo[crc[1:0]], crc[7*crc[1:0]+:7]);
    `checkh(cl2[0], crc[6:0]);
    `checkh(cl2[3], crc[27:21]);
    `checkh(wc3[0], crc[6:0]);
    `checkh(wc3[3], crc[27:21]);
    `checkh(fxo, 7'h7f);
    `checkh(locx, crc[6:0] ^ crc[13:7]);
    `checkh(vi.arr[1], crc[13:7]);
    objs[0].val = cyc;
    objs[1].val = cyc + 1;
    qs[0].push_back(cyc);
    qs[1].push_front(cyc);
    `checkh(objs[0].val, cyc);
    `checkh(objs[1].val, cyc + 1);
    `checkh(qs[0].size(), cyc + 1);
    `checkh(qs[0][cyc], cyc);
    `checkh(qs[1][0], cyc);
    `checkh(vis[1].arr[0], crc[20:14]);
    `checkh(pout[0], ~crc[6:0]);
    `checkh(pout[1], crc[13:7] + 7'd1);
    `checkh(evcnt0, cyc);
    `checkh(evcnt1, cyc / 2);
    if (cyc > 0) begin
      `checkh(q[1], crc_q[13:7]);
      `checkh(q[2], crc_q[20:14]);
      `checkh(q[3], crc_q[27:21]);
    end
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

interface ifc;
  logic [6:0] arr [2];  // No split: accessed via a virtual interface
endinterface

// Not inlined, with unpacked ports. The references are aliased to the connected variables,
// so the ports are only copied whole to/from those, which are split, so split too.
module psub (
    input logic [6:0] pin [2],  // Split 1
    output logic [6:0] pout [2]  // Split 1
);
  /*verilator no_inline_module*/
  always_comb begin
    pout[0] = ~pin[0];
    pout[1] = pin[1] + 7'd1;
  end
endmodule

// Not inlined, so the same variable is split in two scopes
module sub (
    input clk,
    input [63:0] crc
);
  /*verilator no_inline_module*/

  logic [6:0] arr [2];  // Split 1

  always_comb begin
    arr[0] = crc[6:0];
    arr[1] = ~crc[13:7];
  end

  always @(posedge clk) begin
    `checkh(arr[0], crc[6:0]);
    `checkh(arr[1], ~crc[13:7]);
  end

endmodule
