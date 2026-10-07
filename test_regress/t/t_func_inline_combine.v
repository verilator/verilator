// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Geza Lore
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// The variables of the inlined calls of 'f' should have the same names in
// all instances of 'sub', so the logic can be shared between them.
module sub (
    input clk,
    input [7:0] d,
    output logic [7:0] q
);
  /* verilator no_inline_module */
  function automatic logic [7:0] f(input logic [7:0] a, input logic [7:0] b);
    logic [7:0] t;
    t = a ^ b;
    return t + {a[3:0], b[7:4]};
  endfunction
  logic [7:0] r = 0, s = 0;
  always_ff @(posedge clk) begin
    r <= f(r, s) ^ d;
    s <= f(s, d);
  end
  assign q = r;
endmodule

module t (
    input clk
);
  function automatic logic [7:0] f(input logic [7:0] a, input logic [7:0] b);
    logic [7:0] t;
    t = a ^ b;
    return t + {a[3:0], b[7:4]};
  endfunction

  integer cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;
  wire [7:0] d = crc[7:0];

  wire [7:0] q0, q1, q2;
  sub u0 (.clk, .d(d), .q(q0));
  sub u1 (.clk, .d(d), .q(q1));
  sub u2 (.clk, .d(d), .q(q2));

  // Reference model
  logic [7:0] rr = 0, rs = 0;
  always_ff @(posedge clk) begin
    rr <= f(rr, rs) ^ d;
    rs <= f(rs, d);
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    `checkh(q0, rr);
    `checkh(q1, rr);
    `checkh(q2, rr);
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
