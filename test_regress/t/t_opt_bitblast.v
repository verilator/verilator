// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Automatic bitblasting of packed variables. Variables expected to be split are marked with a
// 'Split N' comment, where N is the number of fragments.

typedef struct packed {
  logic [4:0] a;
  logic [6:0] b;
} ps_t;

module t (
    input clk
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;

  // Disjoint selects, chain through the bits, would be UNOPTFLAT if not split
  logic [7:0] ach;  // Split 2
  // Identical selects, with bits never written between them
  logic [11:0] aid;  // Split 3
  // Only one bit referenced, unused bits at the edges dropped
  logic [99:0] anr;  // Split 1
  // Packed struct with selects spanning members, so not split by V3Decompose
  ps_t aspan;  // Split 3
  // Ascending range
  // verilator lint_off ASCRANGE
  logic [0:7] asc;  // Split 2
  // verilator lint_on ASCRANGE
  // Written other than by an assignment, one fragment
  logic [15:0] ass;  // Split 2
  // Overlapping selects
  logic [7:0] aov;  // No split: overlapping selects
  // Variable index
  logic [7:0] avi;  // No split: variable index
  // Partially out of range select, the LSB in range, but not the MSB
  logic [7:0] aoob;  // No split: out of range select
  // Interface variable accessed via a virtual interface
  ifc u_ifc ();
  virtual ifc vi = u_ifc;

  assign ach[3:0] = crc[3:0];
  assign ach[7:4] = ach[3:0] + crc[7:4];

  assign aid[3:0] = crc[3:0];
  assign aid[11:8] = aid[3:0] ^ crc[11:8];

  assign anr[2] = crc[2];

  assign aspan[8:3] = crc[5:0];
  assign aspan[11:9] = {2'b0, ^aspan[8:3]} + crc[8:6];
  assign aspan[2:0] = crc[11:9];

  assign asc[0:3] = crc[3:0];
  assign asc[4:7] = asc[0:3] ^ crc[7:4];

  always @(posedge clk) void'($sscanf("a5", "%x", ass[7:0]));
  assign ass[15:8] = crc[7:0];

  assign aov[3:0] = crc[3:0];
  assign aov[7:4] = crc[7:4];

  // verilator lint_off SELRANGE
  always_comb begin
    aoob[5:0] = crc[5:0];
    aoob[9:6] = crc[9:6];
  end
  // verilator lint_on SELRANGE

  assign avi[3:0] = crc[3:0];
  assign avi[7:4] = crc[7:4];

  assign u_ifc.v[3:0] = crc[3:0];
  assign u_ifc.v[7:4] = crc[7:4];

  subq u_subq ();

  // Instances of the same module, split differently
  subm u_m0 ();
  subm u_m1 ();

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    `checkh(ach[7:4], crc[3:0] + crc[7:4]);
    `checkh(aid[11:8], crc[3:0] ^ crc[11:8]);
    `checkh(aid[3:0], crc[3:0]);
    `checkh(anr[2], crc[2]);
    `checkh(aspan[11:9], {2'b0, ^crc[5:0]} + crc[8:6]);
    `checkh(aspan[8:3], crc[5:0]);
    `checkh(aspan[2:0], crc[11:9]);
    `checkh(asc[4:7], crc[3:0] ^ crc[7:4]);
    if (cyc > 0) `checkh(ass[7:0], 8'ha5);
    `checkh(ass[15:8], crc[7:0]);
    `checkh(aov[5:2], crc[5:2]);
    `checkh(avi[crc[2:0]], crc[{3'b0, crc[2:0]}]);
    `checkh(aoob[7:6], crc[7:6]);
    `checkh(aoob[5:0], crc[5:0]);
    `checkh(vi.v[7:4], crc[7:4]);
    // Whole read, so only this instance is not split
    `checkh(u_m1.m, {crc[3:0] + crc[7:4], crc[3:0]});
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

interface ifc;
  logic [7:0] v;  // No split: accessed via a virtual interface
endinterface

// Not inlined, and with only clocked logic, so without combinational logic to drive the traced
// original variable from its fragments with
module subq;
  /*verilator no_inline_module*/

  logic [7:0] r;  // Split 2
  logic [63:0] crc_q = '0;

  always_ff @(posedge t.clk) r[3:0] <= t.crc[3:0];
  always_ff @(posedge t.clk) r[7:4] <= t.crc[7:4];
  always_ff @(posedge t.clk) crc_q <= t.crc;

  always @(posedge t.clk) begin
    if (crc_q != '0) begin
      `checkh(r[3:0], crc_q[3:0]);
      `checkh(r[7:4], crc_q[7:4]);
    end
  end

endmodule

// Not inlined, instantiated twice, with one instance read whole hierarchically
module subm;
  /*verilator no_inline_module*/

  logic [7:0] m;  // Split 2, only in 'u_m0'

  assign m[3:0] = t.crc[3:0];
  assign m[7:4] = m[3:0] + t.crc[7:4];

  always @(posedge t.clk) begin
    `checkh(m[7:4], t.crc[3:0] + t.crc[7:4]);
  end

endmodule
