// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test iff (enable) guard: sampling is gated by the enable condition.
// Covers iff on explicit value bins, default bin, array bins,
// simple 2-step transition, and 3-step transition.
// Also covers coverpoint iff propagation into crosses and cross-level iff guards.
//
// Also covers compound iff expressions (&&, ||, unary !, bit/part-select,
// relational compare, parenthesized bitwise, and a concatenation-valued
// coverpoint with a compound iff).  Previously any iff that was not a bare
// reference or a unary ! tripped an internal error ("Unexpected '...'
// expression under 'COVERPOINT'") because the iff child was widthed with no
// context.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class CrossIffEmbedded;
  bit a;
  bit b;
  bit enabled;

  // cross-level iff using an enclosing class member
  covergroup cg;
    cp_a: coverpoint a {bins one = {1};}
    cp_b: coverpoint b {bins one = {1};}
    cross_ab: cross cp_a, cp_b iff (this.enabled);
  endgroup

  function new();
    cg = new;
  endfunction

  function void observe(bit next_a, bit next_b, bit next_enabled);
    a = next_a;
    b = next_b;
    enabled = next_enabled;
    cg.sample();
  endfunction
endclass

module t;
  logic enable;
  int value;

  // Signals for the compound-iff covergroups below
  logic m_is_read;
  logic [3:0] m_be;
  logic [1:0] m_a;
  logic [1:0] m_b;
  int count;

  // iff on explicit value bins
  covergroup cg_iff;
    cp_value: coverpoint value iff (enable) {
      bins disabled_lo = {1}; bins disabled_hi = {2}; bins enabled_lo = {3}; bins enabled_hi = {4};
    }
  endgroup

  // iff on default bin
  covergroup cg_default_iff;
    cp: coverpoint value iff (enable) {
      bins known = {10};
      bins def = default;  // default bin with coverpoint-level iff
    }
  endgroup

  // iff on array bins
  covergroup cg_array_iff;
    cp: coverpoint value iff (enable) {
      bins arr[] = {5, 6, 7};  // array bins, all gated by iff
    }
  endgroup

  // iff on 2-step transition
  covergroup cg_trans2_iff;
    cp: coverpoint value iff (enable) {bins t2 = (1 => 2);}
  endgroup

  // iff on 3-step transition
  covergroup cg_trans3_iff;
    cp: coverpoint value iff (enable) {bins t3 = (1 => 2 => 3);}
  endgroup

  // --- compound iff expressions ---

  // unary ! combined with && and a bit-select, on a concatenation-valued
  // coverpoint expression -- the exact reported shape.
  covergroup cg_and;
    cp_concat: coverpoint {
      m_a[0], m_b[0]
    } iff (!m_is_read && m_be[0]) {
      bins b00 = {2'b00}; bins b01 = {2'b01}; bins b10 = {2'b10}; bins b11 = {2'b11};
    }
  endgroup

  // logical || guard
  covergroup cg_or;
    cp: coverpoint count iff (m_be[0] || m_be[1]) {bins lo = {1}; bins hi = {2};}
  endgroup

  // part-select compare guard
  covergroup cg_part;
    cp: coverpoint count iff (m_be[3:0] != 0) {bins one = {1};}
  endgroup

  // relational compare guard
  covergroup cg_rel;
    cp: coverpoint count iff (count > 3) {bins five = {5}; bins two = {2};}
  endgroup

  // parenthesized bitwise guard
  covergroup cg_bitw;
    cp: coverpoint count iff ((m_a & m_b) == 2'b10) {bins seven = {7};}
  endgroup

  // coverpoint-level iff only; the cross has no guard
  covergroup cg_cross_coverpoint_iff with function sample(
      bit a, bit b, bit enable_a, bit enable_b);
    cp_a: coverpoint a iff (enable_a) {bins one = {1};}
    cp_b: coverpoint b iff (enable_b) {bins one = {1};}
    cross_ab: cross cp_a, cp_b;
  endgroup

  // coverpoint-level and cross-level iff together
  covergroup cg_cross_iff with function sample(
      bit a, bit b, bit enable_a, bit enable_b, bit enable_cross);
    cp_a: coverpoint a iff (enable_a) {bins one = {1};}
    cp_b: coverpoint b iff (enable_b) {bins one = {1};}
    cross_ab: cross cp_a, cp_b iff (enable_cross && (a == b));
  endgroup

  // cross-level iff only; also exercise an unnamed cross
  covergroup cg_cross_iff_unnamed with function sample(bit a, bit b, bit disable_cross);
    cp_a: coverpoint a {bins one = {1};}
    cp_b: coverpoint b {bins one = {1};}
    cross cp_a, cp_b iff (!disable_cross) {}
  endgroup

  cg_iff cg1 = new;
  cg_default_iff cg2 = new;
  cg_array_iff cg3 = new;
  cg_trans2_iff cg4 = new;
  cg_trans3_iff cg5 = new;
  cg_and ca = new;
  cg_or co = new;
  cg_part cpp = new;
  cg_rel cr = new;
  cg_bitw cb = new;
  cg_cross_coverpoint_iff cxc = new;
  cg_cross_iff cx = new;
  cg_cross_iff_unnamed cxu = new;
  CrossIffEmbedded cxe = new;

  initial begin
    cxc.sample(1, 1, 0, 1);
    cxc.sample(1, 1, 1, 0);
    cxc.sample(1, 1, 1, 1);
    cx.sample(1, 1, 0, 1, 1);
    cx.sample(1, 1, 1, 0, 1);
    cx.sample(1, 1, 1, 1, 0);
    cx.sample(1, 1, 1, 1, 1);
    cxu.sample(1, 1, 1);
    cxu.sample(1, 1, 0);
    cxe.observe(1, 1, 0);
    cxe.observe(1, 1, 1);

    // Sample disabled_lo and disabled_hi with enable=0 -- must not be recorded
    enable = 0;
    value = 1;
    cg1.sample();
    value = 2;
    cg1.sample();
    `checkr(cg1.get_inst_coverage(), 0.0);

    // Sample enabled_lo and enabled_hi with enable=1 -- must be recorded
    enable = 1;
    value = 3;
    cg1.sample();
    `checkr(cg1.get_inst_coverage(), 25.0);
    value = 4;
    cg1.sample();
    `checkr(cg1.get_inst_coverage(), 50.0);

    // cg2: default bin -- enable=1 lets known and default through
    enable = 1;
    value = 10;
    cg2.sample();  // hits 'known'
    `checkr(cg2.get_inst_coverage(), 100.0);  // 1/1: only 'known' counts (default excluded, LRM 19.5)
    value = 99;
    cg2.sample();  // hits 'def' (default)
    `checkr(cg2.get_inst_coverage(), 100.0);
    enable = 0;
    value = 99;
    cg2.sample();  // gated by iff -- must NOT hit 'def'
    `checkr(cg2.get_inst_coverage(), 100.0);

    // cg3: array bins with iff (3 bins: arr[5], arr[6], arr[7])
    // 1/3 hit -> 33.3% (not a clean binary fraction; no checkr)
    enable = 1;
    value = 5;
    cg3.sample();  // arr[5] hit
    enable = 0;
    value = 6;
    cg3.sample();  // gated

    // cg4: 2-step transition with iff
    enable = 1;
    value = 1;
    cg4.sample();
    `checkr(cg4.get_inst_coverage(), 0.0);
    value = 2;
    cg4.sample();  // (1=>2) hit with enable=1
    `checkr(cg4.get_inst_coverage(), 100.0);
    enable = 0;
    value = 1;
    cg4.sample();
    value = 2;
    cg4.sample();  // (1=>2) gated by iff
    `checkr(cg4.get_inst_coverage(), 100.0);

    // cg5: 3-step transition with iff
    enable = 1;
    value = 1;
    cg5.sample();
    value = 2;
    cg5.sample();  // mid-sequence, enable=1
    enable = 0;
    value = 3;
    cg5.sample();  // iff is disabled at step 3 - incomplete sequence is discarded
    `checkr(cg5.get_inst_coverage(), 0.0);
    enable = 1;
    value = 1;
    cg5.sample();
    value = 2;
    cg5.sample();
    value = 3;
    cg5.sample();  // (1=>2=>3) fully hit with enable=1
    `checkr(cg5.get_inst_coverage(), 100.0);

    // --- compound iff expressions ---
    // cg_and: guard true -> {0,1}=2'b01 sampled into b01
    m_is_read = 0;
    m_be = 4'b0001;
    m_a = 2'b10;
    m_b = 2'b11;  // m_a[0]=0,m_b[0]=1 -> 2'b01
    ca.sample();  // b01 hit
    `checkr(ca.get_inst_coverage(), 25.0);
    m_is_read = 1;
    m_a = 2'b11;
    m_b = 2'b11;  // guard false -> gated
    ca.sample();
    `checkr(ca.get_inst_coverage(), 25.0);

    // cg_or: guard true via bit1
    m_be = 4'b0010;
    count = 1;
    co.sample();  // lo hit
    `checkr(co.get_inst_coverage(), 50.0);
    m_be = 4'b0000;
    count = 2;
    co.sample();  // gated
    `checkr(co.get_inst_coverage(), 50.0);

    // cg_part: part-select != 0
    m_be = 4'b1000;
    count = 1;
    cpp.sample();  // one hit
    `checkr(cpp.get_inst_coverage(), 100.0);
    m_be = 4'b0000;
    count = 1;
    cpp.sample();  // gated
    `checkr(cpp.get_inst_coverage(), 100.0);

    // cg_rel: count > 3
    count = 5;
    cr.sample();  // five hit (5>3)
    `checkr(cr.get_inst_coverage(), 50.0);
    count = 2;
    cr.sample();  // two gated (2>3 false)
    `checkr(cr.get_inst_coverage(), 50.0);

    // cg_bitw: (m_a & m_b) == 2'b10
    m_a = 2'b10;
    m_b = 2'b11;
    count = 7;
    cb.sample();  // seven hit
    `checkr(cb.get_inst_coverage(), 100.0);
    m_a = 2'b00;
    m_b = 2'b11;
    count = 7;
    cb.sample();  // gated
    `checkr(cb.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
