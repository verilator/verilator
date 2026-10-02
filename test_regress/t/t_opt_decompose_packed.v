// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Automatic splitting of packed arrays and structs into their elements and members
// Variables expected to be split are marked with a 'Split N' comment, where N is the
// number of variables split: the variable itself, and its components split further.

typedef struct packed {
  logic [4:0] a;
  logic [6:0] b;
} ps_t;

typedef struct packed {
  logic [5:0] hi;
  logic [5:0] lo;
} pw_t;

typedef union packed {
  logic [11:0] w;
  ps_t s;
} pu_t;

typedef struct packed {
  logic [1:0][2:0] v;
  logic [3:0] w;
} pv_t;

typedef struct packed {
  logic [3:0] g;
  logic [3:0] h;
} pin_t;

typedef struct packed {
  pin_t f;
  logic [3:0] e;
} pout_t;

typedef struct packed {
  pin_t a;
} pone_t;

typedef logic bit_t;

module t (
    input clk
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;
  logic [63:0] crc_q = '0;

  // Packed struct, chain through members, would be UNOPTFLAT if not split
  ps_t ps;  // Split 1
  // Packed array, descending, chain through elements
  logic [3:0][2:0] pd;  // Split 1
  // Packed array, ascending
  // verilator lint_off ASCRANGE
  logic [0:3][4:0] pa;  // Split 1
  // verilator lint_on ASCRANGE
  // Packed array, non-zero based
  logic [4:1][3:0] pnz;  // Split 1
  // Packed array of packed structs, the elements are split too
  ps_t [1:0] pas;  // Split 3
  // Packed array of packed structs, the elements are split too, copied to a different layout,
  // which is split, and to a plain vector, which cannot be split
  ps_t [1:0] prr;  // Split 3
  logic [3:0][5:0] lrr;  // Split 1
  logic [23:0] frr;
  // Recursive, 4 dimensional, chain through the innermost elements, each level of packed
  // array is split: 1 + 3 elements + 3 * 2 sub-elements
  logic [2:0][1:0][3:0][1:0] p4;  // Split 10
  logic [47:0] p4_flat;
  // Recursive, ascending and non-zero based dimensions
  // verilator lint_off ASCRANGE
  logic [3:1][0:1][1:3][1:0] p4m;  // Split 10
  // verilator lint_on ASCRANGE
  logic [35:0] p4m_flat;
  // Recursive, only the element selected from is split further
  logic [1:0][1:0][3:0] p3p;  // Split 2
  // Recursive, array of structs with packed array members: 1 + 2 elements + 2 'v' members
  pv_t [1:0] pav;  // Split 5
  // Whole copy, same layout
  ps_t ps_cp;  // Split 1
  // Copied from, and to a plain vector
  logic [11:0] flat_in;
  ps_t pfrom;  // Split 1
  logic [11:0] flat_out;
  // Copied from, and to a bit select
  ps_t psel;  // Split 1
  logic [15:0] flat_sel;
  // Concatenation aligned with the members
  ps_t pcat;  // Split 1
  // Concatenation with an expression assigned to a member that is split itself
  pout_t pnest;  // Split 2: component value assigned to a temporary first
  logic [7:0] pnest_f;
  // Concatenation with a variable reference spanning members
  logic [3:0] n4;
  logic [7:0] n8;
  ps_t pcv;  // Split 1
  // Replication of a variable reference spanning members
  ps_t prep;  // Split 1
  // Concatenation with a constant spanning members
  ps_t pcc;  // Split 1
  // Concatenation with a select path spanning members
  ps_t pcx;  // Split 1
  // Concatenation with another expression spanning members, assigned to a temporary first
  ps_t pcy;  // Split 1
  logic [7:0] pcy_lo;
  // Concatenation reading the variable assigned, blocking swap of the members, assigned to a
  // temporary first
  pw_t psw;  // Split 1
  logic [11:0] swr;
  // Assigned from itself through its only member, so the sides are the same bits
  pone_t pov;  // Split 2
  logic [7:0] povr;
  // Concatenation reading the variable assigned, non-blocking swap of the members
  pw_t pswd;  // Split 1
  logic [11:0] swrd;
  // Constant
  ps_t pk;  // Split 1
  pw_t pshr;  // Split 1
  logic [5:0] shr[2];
  // Result from an automatic local, reset on entry
  logic [6:0] locx;
  // Non-blocking assignments
  ps_t q;  // Split 1
  // Select spanning members
  ps_t pspan;  // No split: select spans members
  // Variable index
  logic [3:0][2:0] pvix;  // No split: variable index
  // Read whole in an expression
  ps_t pwhole;  // No split: referenced whole
  // Copy between different layouts
  logic [2:0][3:0] l34;  // Split 1
  logic [3:0][2:0] l43;  // Split 1
  // Only copied whole, so not split
  ps_t pw1;  // No split: only copied whole
  ps_t pw2;  // No split: only copied whole
  logic [11:0] pw_out;
  // Only copied whole, but copied to a variable that is split, so split too
  ps_t pl1;  // Split 1
  ps_t pl2;  // Split 1
  // Packed union
  pu_t pu;  // No split: packed union
  // Plain vector
  logic [7:0] vec;
  // Plain vector, as a packed array of single bits
  bit_t [7:0] bvec;  // No split: plain vector
  // Plain vector, as a packed array of single bit elements
  logic [7:0][0:0] zvec;  // No split: plain vector
  // Expressions spanning members, the selects of the members pushed into the operations
  ps_t psc;  // Split 1
  ps_t psb;  // Split 1
  ps_t psn;  // Split 1
  ps_t pse;  // Split 1
  pw_t pwe;  // Split 1
  ps_t psr;  // Split 1
  ps_t pst;  // Split 1
  // Expression within one member, evaluated once
  ps_t pone;  // Split 1
  // Variable bit select spanning members, assigned to a temporary first
  ps_t pvt;  // Split 1
  // Replicated expression spanning members, assigned to a temporary first
  ps_t prx;  // Split 1
  logic [3:0] prx_x;
  // Condition not cheap, assigned to a temporary first
  ps_t pcn;  // Split 1

  assign ps.a = crc[4:0];
  assign ps.b = 7'(ps.a) + 7'd3;

  assign pd[0] = crc[2:0];
  for (genvar g = 1; g < 4; g++) begin : gen_pd
    assign pd[g] = pd[g-1] + 3'd1;
  end

  assign pa[0] = crc[4:0];
  for (genvar g = 1; g < 4; g++) begin : gen_pa
    assign pa[g] = pa[g-1] ^ crc[g*5+:5];
  end

  assign pnz[1] = crc[3:0];
  for (genvar g = 2; g <= 4; g++) begin : gen_pnz
    assign pnz[g] = pnz[g-1] + 4'd2;
  end

  // Expected value of element 'n' of 'p4' and 'p4m', in declaration order
  function automatic logic [1:0] p4Sum(int n);
    logic [1:0] r = 2'b0;
    for (int m = 0; m <= n; m++) r = r + crc[2*m+:2];
    return r;
  endfunction
  function automatic logic [1:0] p4mXor(int n);
    logic [1:0] r = 2'b0;
    for (int m = 0; m <= n; m++) r = r ^ crc[2*m+:2];
    return r;
  endfunction

  for (genvar i = 0; i < 3; i++) begin : gen_p4_i
    for (genvar j = 0; j < 2; j++) begin : gen_p4_j
      for (genvar k = 0; k < 4; k++) begin : gen_p4_k
        localparam int N = (i * 2 + j) * 4 + k;
        if (N == 0) begin : gen_first
          assign p4[i][j][k] = crc[1:0];
        end else begin : gen_rest
          assign p4[i][j][k] = p4[(N-1)/8][((N-1)/4)%2][(N-1)%4] + crc[2*N+:2];
        end
      end
    end
  end
  assign p4_flat = p4;

  for (genvar i = 1; i <= 3; i++) begin : gen_p4m_i
    for (genvar j = 0; j <= 1; j++) begin : gen_p4m_j
      for (genvar k = 1; k <= 3; k++) begin : gen_p4m_k
        localparam int N = ((i - 1) * 2 + j) * 3 + (k - 1);
        if (N == 0) begin : gen_first
          assign p4m[i][j][k] = crc[1:0];
        end else begin : gen_rest
          assign p4m[i][j][k] = p4m[(N-1)/6+1][((N-1)/3)%2][(N-1)%3+1] ^ crc[2*N+:2];
        end
      end
    end
  end
  assign p4m_flat = p4m;

  assign p3p[0] = crc[7:0];
  assign p3p[1][0] = crc[11:8];
  assign p3p[1][1] = p3p[1][0] + 4'd1;

  assign pav[0].v[0] = crc[2:0];
  assign pav[0].v[1] = pav[0].v[0] + 3'd1;
  assign pav[0].w = {1'b0, pav[0].v[1]};
  assign pav[1].v[0] = pav[0].w[2:0] ^ crc[5:3];
  assign pav[1].v[1] = pav[1].v[0] + 3'd2;
  assign pav[1].w = crc[9:6];

  always_comb begin
    pas[0].a = crc[4:0];
    pas[0].b = 7'(pas[0].a) ^ crc[11:5];
    pas[1].a = pas[0].b[4:0];
    pas[1].b = 7'(pas[1].a) + 7'd1;
  end

  assign ps_cp = ps;

  assign flat_in = crc[23:12];
  assign pfrom = flat_in;
  assign flat_out = pfrom;
  assign prr = crc[23:0];
  assign lrr = prr;
  assign frr = prr;
  assign psel = crc[35:24];
  assign flat_sel[13:2] = psel;
  assign flat_sel[1:0] = 2'b0;
  assign flat_sel[15:14] = 2'b0;

  assign pcat = {crc[4:0], crc[13:7]};
  assign pnest = {8'(crc[7:0] + 8'd3), crc[11:8]};
  assign pnest_f = crc[7:0] + 8'd3;
  assign n4 = crc[3:0];
  assign n8 = crc[15:8];
  assign pcv = {n4, n8};
  assign prep = {3{n4}};
  assign pcc = {crc[3:0], 8'ha5};
  assign pcx = {crc[3:0], crc[15:8]};
  assign pcy = {crc[3:0], crc[15:8] + 8'd1};
  assign pcy_lo = crc[15:8] + 8'd1;

  assign pw1 = crc[47:36];
  assign pw2 = pw1;
  assign pw_out = pw2;
  assign pl1 = crc[47:36];
  assign pl2 = pl1;

  always_comb pk = 12'h5a3;

  assign psc = crc[0] ? crc[11:0] : 12'h5a3;
  assign psb = (crc[11:0] & crc[23:12]) | ~(crc[35:24] ^ crc[47:36]);
  assign psn = crc[1] ? {crc[3:0], crc[39:32]} : {crc[47:42], crc[5:0]};
  assign pse = 12'(crc[7:0] ^ crc[15:8]);
  assign pwe = 12'(crc[5:0] & crc[11:6]);
  assign psr = {3{crc[3:0]}} ^ crc[11:0];
  assign pst = 12'(crc[23:0] ^ crc[47:24]);
  assign pone = {crc[4:0] + 5'd1, crc[6'(crc[3:0])+:7]};
  assign pvt = crc[6'(crc[3:0])+:12];
  assign prx = {3{4'(crc[7:0] / (crc[15:8] | 8'd1))}};
  assign prx_x = 4'(crc[7:0] / (crc[15:8] | 8'd1));
  assign pcn = (crc[0] ^ crc[5]) ? crc[11:0] : crc[23:12];

  assign pshr = crc[47:36];
  always_comb for (int i = 0; i < 2; i++) shr[i] = 6'(pshr >> (6 * i));

  always_comb begin
    automatic ps_t loc;  // Split 1
    loc.a = crc[4:0];
    loc.b = 7'(loc.a) + crc[11:5];
    locx = loc.b;
  end

  always @(posedge clk) begin
    if (cyc == 0) begin
      psw = crc[11:0];
      swr = crc[11:0];
    end else begin
      psw = {psw.lo, psw.hi};
      swr = {swr[5:0], swr[11:6]};
    end
    `checkh(psw.hi, swr[11:6]);
    `checkh(psw.lo, swr[5:0]);
  end

  always @(posedge clk) begin
    if (cyc == 0) begin
      pov = crc[7:0];
      povr = crc[7:0];
    end else begin
      pov.a = pov;
    end
    `checkh(pov.a.g, povr[7:4]);
    `checkh(pov.a.h, povr[3:0]);
  end

  always @(posedge clk) begin
    if (cyc == 0) begin
      pswd <= crc[11:0];
      swrd <= crc[11:0];
    end else begin
      pswd <= {pswd.lo, pswd.hi};
      swrd <= {swrd[5:0], swrd[11:6]};
    end
    `checkh(pswd.hi, swrd[11:6]);
    `checkh(pswd.lo, swrd[5:0]);
  end

  always_ff @(posedge clk) begin
    q.a <= crc[4:0];
    q.b <= 7'(q.a);
    crc_q <= crc;
  end

  always_comb begin
    pspan.a = crc[4:0];
    pspan.b = crc[11:5];
    pvix[0] = crc[2:0];
    pvix[1] = pvix[0] + 3'd1;
    pvix[2] = pvix[1] + 3'd1;
    pvix[3] = pvix[2] + 3'd1;
    pwhole.a = crc[4:0];
    pwhole.b = crc[11:5];
    l34[0] = crc[3:0];
    l34[1] = l34[0] ^ crc[7:4];
    l34[2] = l34[1] ^ crc[11:8];
    l43 = l34;
    pu.w = crc[11:0];
    vec[3:0] = crc[3:0];
    vec[7:4] = vec[3:0] + 4'd1;
    bvec[0] = crc[0];
    bvec[1] = bvec[0] ^ crc[1];
    bvec[2] = bvec[1] ^ crc[2];
    zvec[0] = crc[0];
    zvec[1] = zvec[0] ^ crc[1];
    zvec[2] = zvec[1] ^ crc[2];
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    `checkh(ps.b, 7'(crc[4:0]) + 7'd3);
    `checkh(pd[3], crc[2:0] + 3'd3);
    `checkh(pd[2][1:0], 2'(crc[2:0] + 3'd2));
    `checkh(pa[3], crc[4:0] ^ crc[9:5] ^ crc[14:10] ^ crc[19:15]);
    `checkh(pnz[4], crc[3:0] + 4'd6);
    `checkh(pas[1].b, 7'(pas[0].b[4:0]) + 7'd1);
    `checkh(pas[0].b, 7'(crc[4:0]) ^ crc[11:5]);
    `checkh(p4[0][0][0], p4Sum(0));
    `checkh(p4[0][1][0], p4Sum(4));
    `checkh(p4[1][0][2], p4Sum(10));
    `checkh(p4[2][1][3], p4Sum(23));
    `checkh(p4_flat[1:0], p4Sum(0));
    `checkh(p4_flat[21:20], p4Sum(10));
    `checkh(p4_flat[47:46], p4Sum(23));
    `checkh(p4m[1][0][1], p4mXor(0));
    `checkh(p4m[1][1][1], p4mXor(3));
    `checkh(p4m[2][1][2], p4mXor(10));
    `checkh(p4m[3][1][3], p4mXor(17));
    // Element [i][j][k] is at bit 12 * (i - 1) + 6 * (1 - j) + 2 * (3 - k)
    `checkh(p4m_flat[11:10], p4mXor(0));
    `checkh(p4m_flat[15:14], p4mXor(10));
    `checkh(p4m_flat[25:24], p4mXor(17));
    `checkh(p3p[0], crc[7:0]);
    `checkh(p3p[1][1], crc[11:8] + 4'd1);
    `checkh(pav[0].w, {1'b0, 3'(crc[2:0] + 3'd1)});
    `checkh(pav[1].v[1], 3'(3'(3'(crc[2:0] + 3'd1) ^ crc[5:3]) + 3'd2));
    `checkh(pav[1].w, crc[9:6]);
    `checkh(ps_cp.a, crc[4:0]);
    `checkh(ps_cp.b, 7'(crc[4:0]) + 7'd3);
    `checkh(pfrom.a, crc[23:19]);
    `checkh(pfrom.b, crc[18:12]);
    `checkh(flat_out, crc[23:12]);
    `checkh(prr[0].a, crc[11:7]);
    `checkh(prr[1].b, crc[18:12]);
    `checkh(lrr[1], crc[11:6]);
    `checkh(lrr[2], crc[17:12]);
    `checkh(frr, crc[23:0]);
    `checkh(psel.a, crc[35:31]);
    `checkh(psel.b, crc[30:24]);
    `checkh(flat_sel, {2'b0, crc[35:24], 2'b0});
    `checkh(pcat.a, crc[4:0]);
    `checkh(pcat.b, crc[13:7]);
    `checkh(pnest.f.g, pnest_f[7:4]);
    `checkh(pnest.f.h, pnest_f[3:0]);
    `checkh(pnest.e, crc[11:8]);
    `checkh(pcv.a, {crc[3:0], crc[15]});
    `checkh(pcv.b, crc[14:8]);
    `checkh(prep.a, {crc[3:0], crc[3]});
    `checkh(prep.b, {crc[2:0], crc[3:0]});
    `checkh(pcc.a, {crc[3:0], 1'b1});
    `checkh(pcc.b, 7'h25);
    `checkh(pcx.a, {crc[3:0], crc[15]});
    `checkh(pcx.b, crc[14:8]);
    `checkh(pcy.a, {crc[3:0], pcy_lo[7]});
    `checkh(pcy.b, pcy_lo[6:0]);
    `checkh(pw_out, crc[47:36]);
    `checkh(pl2.a, crc[47:43]);
    `checkh(pl2.b, crc[42:36]);
    `checkh(pk.a, 5'h0b);
    `checkh(pk.b, 7'h23);
    `checkh(psc.a, crc[0] ? crc[11:7] : 5'h0b);
    `checkh(psc.b, crc[0] ? crc[6:0] : 7'h23);
    `checkh(psb.a, (crc[11:7] & crc[23:19]) | ~(crc[35:31] ^ crc[47:43]));
    `checkh(psb.b, (crc[6:0] & crc[18:12]) | ~(crc[30:24] ^ crc[42:36]));
    `checkh(psn.a, crc[1] ? {crc[3:0], crc[39]} : crc[47:43]);
    `checkh(psn.b, crc[1] ? crc[38:32] : {crc[42], crc[5:0]});
    `checkh(pse.a, {4'b0, crc[7] ^ crc[15]});
    `checkh(pse.b, crc[6:0] ^ crc[14:8]);
    `checkh(pwe.hi, 6'h0);
    `checkh(pwe.lo, crc[5:0] & crc[11:6]);
    `checkh(psr.a, {crc[3:0], crc[3]} ^ crc[11:7]);
    `checkh(psr.b, {crc[2:0], crc[3:0]} ^ crc[6:0]);
    `checkh(pst.a, crc[11:7] ^ crc[35:31]);
    `checkh(pst.b, crc[6:0] ^ crc[30:24]);
    `checkh(pone.a, crc[4:0] + 5'd1);
    `checkh(pone.b, 7'(crc >> crc[3:0]));
    `checkh(pvt.a, 5'(crc >> (crc[3:0] + 7)));
    `checkh(pvt.b, 7'(crc >> crc[3:0]));
    `checkh(prx.a, {prx_x, prx_x[3]});
    `checkh(prx.b, {prx_x[2:0], prx_x});
    `checkh(pcn.a, (crc[0] ^ crc[5]) ? crc[11:7] : crc[23:19]);
    `checkh(pcn.b, (crc[0] ^ crc[5]) ? crc[6:0] : crc[18:12]);
    `checkh(shr[0], crc[41:36]);
    `checkh(shr[1], crc[47:42]);
    `checkh(locx, 7'(crc[4:0]) + crc[11:5]);
    `checkh(pspan[8:3], {crc[1:0], crc[11:8]});
    `checkh(pvix[crc[1:0]], 3'(crc[2:0] + 3'(crc[1:0])));
    `checkh(pwhole ^ 12'hfff, ~{crc[4:0], crc[11:5]});
    `checkh(l43[2], {crc[8] ^ crc[4] ^ crc[0], crc[7:6] ^ crc[3:2]});
    `checkh(l43[0], crc[2:0]);
    `checkh(l43[3], {crc[11:9] ^ crc[7:5] ^ crc[3:1]});
    `checkh(pu.s.a, crc[11:7]);
    `checkh(vec[7:4], crc[3:0] + 4'd1);
    `checkh(bvec[2], crc[2] ^ crc[1] ^ crc[0]);
    `checkh(zvec[2], crc[2] ^ crc[1] ^ crc[0]);
    if (cyc > 1) begin
      `checkh(q.a, crc_q[4:0]);
    end
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  sub u_sub0 (
      .clk(clk),
      .crc(crc)
  );
  sub u_sub1 (
      .clk(clk),
      .crc(~crc)
  );
  subq u_subq ();

endmodule

// Not inlined, so the same variable is split in two scopes
module sub (
    input clk,
    input [63:0] crc
);
  /*verilator no_inline_module*/

  ps_t s;  // Split 1

  always_comb begin
    s.a = crc[4:0];
    s.b = 7'(s.a) ^ crc[11:5];
  end

  always @(posedge clk) begin
    `checkh(s.b, 7'(crc[4:0]) ^ crc[11:5]);
  end

endmodule

// Not inlined, without ports and with only clocked logic, so without combinational logic to
// drive the traced original variable from its components with
module subq;
  /*verilator no_inline_module*/

  ps_t r;  // Split 1
  logic [63:0] crc_q = '0;

  always_ff @(posedge t.clk) begin
    r.a <= t.crc[4:0];
    r.b <= t.crc[11:5];
    crc_q <= t.crc;
  end

  always @(posedge t.clk) begin
    if (crc_q != '0) begin
      `checkh(r.a, crc_q[4:0]);
      `checkh(r.b, crc_q[11:5]);
    end
  end

endmodule
