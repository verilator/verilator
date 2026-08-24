// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test cross coverage compiled with --protect-ids.  --protect-ids obfuscates
// identifiers in the generated C++ for IP protection, and the coverage database must
// be obfuscated too -- exactly as line/toggle coverage points are.  Every covergroup,
// coverpoint, cross and bin name here carries the distinctive "cgsecret" marker so the
// driver can assert (via file_grep_not) that none of them leak into coverage.dat.  The
// get_inst_coverage() self-checks additionally confirm sampling still works when the
// names are hashed.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [1:0] cgsecret_addr;
  logic cgsecret_cmd;

  // Value-bin cross
  covergroup cgsecret_cg;
    cgsecret_cp_addr: coverpoint cgsecret_addr {bins cgsecret_a0 = {0}; bins cgsecret_a1 = {1};}
    cgsecret_cp_cmd: coverpoint cgsecret_cmd {bins cgsecret_rd = {0}; bins cgsecret_wr = {1};}
    cgsecret_ac: cross cgsecret_cp_addr, cgsecret_cp_cmd;
  endgroup

  // Range-bin cross (cross bin names are built at runtime from the range-bin names)
  covergroup cgsecret_cg_rng;
    cgsecret_cp_addr: coverpoint cgsecret_addr {
      bins cgsecret_lo = {[0 : 1]}; bins cgsecret_hi = {[2 : 3]};
    }
    cgsecret_cp_cmd: coverpoint cgsecret_cmd {bins cgsecret_rd = {0}; bins cgsecret_wr = {1};}
    cgsecret_rc: cross cgsecret_cp_addr, cgsecret_cp_cmd;
  endgroup

  cgsecret_cg cg_inst = new;
  cgsecret_cg_rng cg_rng_inst = new;

  initial begin
    // cg_inst: 2 + 2 + 4 = 8 bins; hit all four cross combinations
    cgsecret_addr = 0;
    cgsecret_cmd = 0;
    cg_inst.sample();  // a0 x rd
    cgsecret_addr = 1;
    cgsecret_cmd = 1;
    cg_inst.sample();  // a1 x wr
    cgsecret_addr = 0;
    cgsecret_cmd = 1;
    cg_inst.sample();  // a0 x wr
    cgsecret_addr = 1;
    cgsecret_cmd = 0;
    cg_inst.sample();  // a1 x rd
    `checkr(cg_inst.get_inst_coverage(), 100.0);  // 8/8

    // cg_rng_inst: 2 + 2 + 4 = 8 bins; hit all four cross combinations
    cgsecret_addr = 0;
    cgsecret_cmd = 0;
    cg_rng_inst.sample();  // lo x rd
    cgsecret_addr = 2;
    cgsecret_cmd = 1;
    cg_rng_inst.sample();  // hi x wr
    cgsecret_addr = 1;
    cgsecret_cmd = 1;
    cg_rng_inst.sample();  // lo x wr
    cgsecret_addr = 3;
    cgsecret_cmd = 0;
    cg_rng_inst.sample();  // hi x rd
    `checkr(cg_rng_inst.get_inst_coverage(), 100.0);  // 8/8

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
