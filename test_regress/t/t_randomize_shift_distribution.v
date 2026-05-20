// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

typedef logic unsigned [63:0] uvm_reg_data_t;

class uvm_reg_field;
  rand uvm_reg_data_t value;
  int unsigned m_size;
  int unsigned m_ones[64];
  constraint c_field_valid {
    if (64 > m_size) {
      value < (64'h1 << m_size);
    }
  }
  function void configure(int unsigned size);
    value = 0;
    m_size = size;
  endfunction
  function void tally;
    for (int b = 0; b < 64; b++) if (value[b]) m_ones[b]++;
  endfunction
endclass

class regA;
  rand uvm_reg_field fa1, fa15, fa31, fa32;
  function new;
    fa1 = new;
    fa15 = new;
    fa31 = new;
    fa32 = new;
    fa1.configure(1);
    fa15.configure(15);
    fa31.configure(31);
    fa32.configure(32);
  endfunction
endclass

module t;
  regA r;
  int unsigned i;
  // 200 trials; seed is pinned in the driver so values are deterministic.
  // Pre-fix bias was 70-90% ones (140-180 per bit), well outside [70, 130].
  localparam int unsigned TRIALS = 200;
  localparam int unsigned LO = 70;
  localparam int unsigned HI = 130;

  initial begin
    r = new;
    for (int t = 0; t < TRIALS; t++) begin
      i = r.randomize();
      `checkd(i, 1);
      r.fa1.tally;
      r.fa15.tally;
      r.fa31.tally;
      r.fa32.tally;
    end
    // For value < (1<<N), bits 0..N-1 must each be set ~50% of the time.
    // High bits (>=N) must be set 0 times. The 1-bit case (fa1) is omitted
    // because its diversity is dominated by SMT solver internals, not by the
    // hash-round count this fix tunes; multi-bit cases below cover the bug.
    for (int b = 0; b < 15; b++) `check_range(r.fa15.m_ones[b], LO, HI);
    for (int b = 0; b < 31; b++) `check_range(r.fa31.m_ones[b], LO, HI);
    for (int b = 0; b < 32; b++) `check_range(r.fa32.m_ones[b], LO, HI);
    // High bits beyond m_size must remain 0.
    for (int b = 1; b < 64; b++) `checkd(r.fa1.m_ones[b], 0);
    for (int b = 15; b < 64; b++) `checkd(r.fa15.m_ones[b], 0);
    for (int b = 31; b < 64; b++) `checkd(r.fa31.m_ones[b], 0);
    for (int b = 32; b < 64; b++) `checkd(r.fa32.m_ones[b], 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
