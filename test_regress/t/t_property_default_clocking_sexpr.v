// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Issue #7472 reproducer (default clocking + |=> + throughout).
module wsn (
  input clk,
  input a, b, c, d
);
  default clocking @(posedge clk); endclocking
  int fail = 0;
  assert property (
      a |=> b throughout (c ##1 d)
  ) else fail <= fail + 1;
endmodule

// Explicit @(edge) must override default clocking.
module clk_override (
  input clk_default,
  input clk_explicit,
  input a, b, c, d
);
  default clocking @(posedge clk_default); endclocking
  int default_fail = 0;
  int explicit_fail = 0;
  assert property (a |=> b throughout (c ##1 d))
    else default_fail <= default_fail + 1;
  assert property (@(posedge clk_explicit) a |=> b throughout (c ##1 d))
    else explicit_fail <= explicit_fail + 1;
endmodule

// Explicit `disable iff` must override default disable.
module dgate (
  input clk,
  input rst,
  input a, b, c, d
);
  default clocking @(posedge clk); endclocking
  default disable iff (rst);
  int default_dis_fail = 0;
  int explicit_dis_fail = 0;
  assert property (a |=> b throughout (c ##1 d))
    else default_dis_fail <= default_dis_fail + 1;
  assert property (disable iff (1'b0) a |=> b throughout (c ##1 d))
    else explicit_dis_fail <= explicit_dis_fail + 1;
endmodule

// No defaults, explicit clock -- fix must not alter this path.
module nodef (
  input clk,
  input a, b, c, d
);
  int fail = 0;
  assert property (@(posedge clk) a |=> b throughout (c ##1 d))
    else fail <= fail + 1;
endmodule

module t (
  input clk
);
  integer cyc = 0;
  reg [63:0] crc = '0;

  wire a = crc[0];
  wire b = crc[4];
  wire c = crc[8];
  wire d = crc[12];

  wire clk_alt = ~clk;
  wire rst    = (cyc < 10);

  default clocking @(posedge clk); endclocking
  default disable iff (cyc < 10);

  int count_fail1 = 0;
  int count_fail2 = 0;
  int count_fail3 = 0;
  int count_fail4 = 0;

  // Issue #7472 exact shape.
  assert property (a |=> b throughout (c ##1 d))
    else count_fail1 <= count_fail1 + 1;
  assert property (a |-> b throughout (c ##1 d))
    else count_fail2 <= count_fail2 + 1;
  assert property (a |=> c ##1 d)
    else count_fail3 <= count_fail3 + 1;
  assert property (a |=> b throughout (c throughout (c ##1 d)))
    else count_fail4 <= count_fail4 + 1;

  cover property (a throughout (c ##[1:2] d));
  cover property (a |=> b throughout (c ##1 d));

  // Generate-scope: module foreach must reach inside generate blocks.
  generate
    if (1) begin : g
      int gen_fail = 0;
      assert property (a |=> b throughout (c ##1 d))
        else gen_fail <= gen_fail + 1;
    end
  endgenerate

  wsn          u_wsn      (.clk(clk), .a(a), .b(b), .c(c), .d(d));
  clk_override u_override (.clk_default(clk), .clk_explicit(clk_alt),
                           .a(a), .b(b), .c(c), .d(d));
  dgate        u_dgate    (.clk(clk), .rst(rst), .a(a), .b(b), .c(c), .d(d));
  nodef        u_nodef    (.clk(clk), .a(a), .b(b), .c(c), .d(d));

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkd(count_fail1, 35);
      `checkd(count_fail2, 36);
      `checkd(count_fail3, 29);
      `checkd(count_fail4, 35);
      `checkd(u_wsn.fail,                  39);
      `checkd(u_override.default_fail,     39);
      `checkd(u_override.explicit_fail,    39);
      `checkd(u_dgate.default_dis_fail,    35);
      `checkd(u_dgate.explicit_dis_fail,   39);
      `checkd(u_nodef.fail,                39);
      `checkd(g.gen_fail,                  35);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
