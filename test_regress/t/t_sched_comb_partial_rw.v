// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// An always_comb or always_latch driving some bits of a packed variable, and
// reading other bits of the same variable that are driven elsewhere.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  bit [63:0] crc = 64'h5aef0c8d_d70a4497;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // verilator lint_off UNOPTFLAT
  logic [8:0] p;
  // verilator lint_on UNOPTFLAT
  assign p[8] = ^crc[3:0];
  always_comb begin
    p[7:0] = '0;
    if (p[8]) p[7:0] = 8'h3C;
  end
  always @(posedge clk) `checkh(p, {^crc[3:0], (^crc[3:0]) ? 8'h3C : 8'h00});

  // Enabled for 4 cycles at a time, while q[8] changes more often. The enable
  // changes on the other clock edge, so the value latched is not racy.
  bit en;
  always @(negedge clk) en <= cyc[2];
  // verilator lint_off UNOPTFLAT
  logic [8:0] q;
  // verilator lint_on UNOPTFLAT
  assign q[8] = ^crc[7:4];
  always_latch begin
    if (en) begin
      q[7:0] = '0;
      if (q[8]) q[7:0] = 8'hA5;
    end
  end
  // Reference, not reading the variable it writes
  logic [7:0] q_exp;
  always_latch if (en) q_exp = (^crc[7:4]) ? 8'hA5 : 8'h00;
  // Both are first enabled in cycle 4
  always @(posedge clk) if (cyc >= 4) `checkh(q, {^crc[7:4], q_exp});

endmodule
