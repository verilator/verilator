// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Graeme Smecher
// SPDX-License-Identifier: CC0-1.0

// Input-only ports tested for Z (as vendor cell models do, to give an unconnected
// pin a default) on instances below the top: a port bit is Z only when its
// connection is undriven. See also t_tri_compass, for a top-level input.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  reg clk = 1'b0;
  always #5 clk = ~clk;

  integer cyc = 0;
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Test: unconnected before connected instances of the same module
  wire z_unc_first;
  zt zt_unc_first (
      .i(),
      .o(z_unc_first)
  );
  always @(negedge clk) `checkh(z_unc_first, 1'b1);

  // Test: two-state expression is driven
  wire z_expr;
  zt zt_expr (
      .i(crc[1] ^ crc[2]),
      .o(z_expr)
  );
  always @(negedge clk) `checkh(z_expr, 1'b0);

  // Test: constant is driven
  wire z_const;
  zt zt_const (
      .i(1'b1),
      .o(z_const)
  );
  always @(negedge clk) `checkh(z_const, 1'b0);

  // Test: tristate net is Z exactly when not enabled
  wire tn = crc[3] ? crc[4] : 1'bz;
  wire z_tri;
  zt zt_tri (
      .i(tn),
      .o(z_tri)
  );
  always @(negedge clk) `checkh(z_tri, ~crc[3]);

  // Test: unconnected after connected instances of the same module
  wire z_unc_last;
  zt zt_unc_last (
      .i(),
      .o(z_unc_last)
  );
  always @(negedge clk) `checkh(z_unc_last, 1'b1);

  // Test: unconnected pin takes the module's default (as UNISIM's WE)
  wire pu_unc;
  pu pu_unc_i (
      .we(),
      .o(pu_unc)
  );
  always @(negedge clk) `checkh(pu_unc, 1'b1);

  // Test: connected pin overrides the default
  wire pu_drv;
  pu pu_drv_i (
      .we(crc[5]),
      .o(pu_drv)
  );
  always @(negedge clk) `checkh(pu_drv, crc[5]);

  // Test: per-bit Z of a partly tristate connection
  wire [2:0] tn3 = crc[6] ? crc[9:7] : 3'bz;
  wire [7:1] zw_bits;
  ztw ztw (
      .i({tn3, crc[13:10]}),
      .z(zw_bits)
  );
  always @(negedge clk) `checkh(zw_bits, {{3{~crc[6]}}, 4'b0});

  // Test: unconnected wide port is Z in every bit
  wire [7:1] zw_unc;
  ztw ztw_unc (
      .i(),
      .z(zw_unc)
  );
  always @(negedge clk) `checkh(zw_unc, 7'h7f);

  // Test: tristate net with two drivers is Z when neither drives
  wire md;
  assign md = crc[16] ? crc[17] : 1'bz;
  assign md = crc[18] ? crc[19] : 1'bz;
  wire z_md;
  zt zt_md (
      .i(md),
      .o(z_md)
  );
  always @(negedge clk) `checkh(z_md, ~(crc[16] | crc[18]));

  // Test: through a module that passes its own input on, and also reads it
  wire tn_mid = crc[20] ? crc[21] : 1'bz;
  wire [2:0] z_mid;
  wire [2:0] p_mid;
  mid mid_unc (
      .a(),
      .o(z_mid[0]),
      .p(p_mid[0])
  );
  mid mid_tri (
      .a(tn_mid),
      .o(z_mid[1]),
      .p(p_mid[1])
  );
  mid mid_drv (
      .a(crc[22]),
      .o(z_mid[2]),
      .p(p_mid[2])
  );
  always @(negedge clk) begin
    `checkh(z_mid, {1'b0, ~crc[20], 1'b1});
    `checkh(p_mid[2], crc[22]);
  end

  // Test: two modules deep
  wire tn_deep = crc[23] ? crc[24] : 1'bz;
  wire z_deep;
  deep deep (
      .a(tn_deep),
      .o(z_deep)
  );
  always @(negedge clk) `checkh(z_deep, ~crc[23]);

  // Test: through a module that reorders selects of its input
  wire [2:0] tn_swz = crc[25] ? crc[28:26] : 3'bz;
  wire [7:1] z_swz;
  swz swz (
      .a({tn_swz, crc[32:29]}),
      .z(z_swz)
  );
  always @(negedge clk) `checkh(z_swz, {4'b0, {3{~crc[25]}}});

  // Test: an operator on a module's inputs is never Z
  wire tn_op = crc[33] ? crc[34] : 1'bz;
  wire [1:0] z_op;
  op op (
      .a(tn_op),
      .b(crc[35]),
      .z(z_op)
  );
  always @(negedge clk) `checkh(z_op, 2'b0);

  // Test: through a variable select of a module's input; out of range is X (#9115)
  wire [2:0] tn_vs = crc[36] ? crc[39:37] : 3'bz;
  wire z_vs;
  vsel vsel (
      .a(tn_vs),
      .idx(crc[41:40]),
      .z(z_vs)
  );
  always @(negedge clk) `checkh(z_vs, (crc[41:40] != 2'd3) & ~crc[36]);

  // Test: variable select of a tristate net; out of range is X (#9115)
  wire [2:0] tn_sel = crc[46] ? crc[49:47] : 3'bz;
  wire [1:0] idx_sel = crc[51:50];
  wire z_sel = (tn_sel[idx_sel] === 1'bz);
  always @(negedge clk) `checkh(z_sel, (idx_sel != 2'd3) & ~crc[46]);

  // Test: through a conditional choosing between a module's inputs
  wire tn_cd = crc[42] ? crc[43] : 1'bz;
  wire z_cd;
  cond cond (
      .a(tn_cd),
      .b(crc[44]),
      .s(crc[45]),
      .z(z_cd)
  );
  always @(negedge clk) `checkh(z_cd, ~crc[45] & ~crc[42]);
endmodule

module cond (
    input wire a,
    input wire b,
    input wire s,
    output wire z
);
  zt zt (
      .i(s ? b : a),
      .o(z)
  );
endmodule

module vsel (
    input wire [2:0] a,
    input wire [1:0] idx,
    output wire z
);
  zt zt (
      .i(a[idx]),
      .o(z)
  );
endmodule

module op (
    input wire a,
    input wire b,
    output wire [1:0] z
);
  zt zt_not (
      .i(~a),
      .o(z[0])
  );
  zt zt_and (
      .i(a & b),
      .o(z[1])
  );
endmodule

module mid (
    input wire a,
    output wire o,
    output wire p
);
  zt zt (
      .i(a),
      .o(o)
  );
  assign p = a;
endmodule

module deep (
    input wire a,
    output wire o
);
  wire p;
  mid mid (
      .a(a),
      .o(o),
      .p(p)
  );
endmodule

module swz (
    input wire [7:1] a,
    output wire [7:1] z
);
  ztw ztw (
      .i({a[4:1], a[7:5]}),
      .z(z)
  );
endmodule

module zt (
    input wire i,
    output wire o
);
  assign o = (i === 1'bz);
endmodule

module pu (
    input wire we,
    output wire o
);
  wire we_in = (we === 1'bz) || we;
  assign o = we_in;
endmodule

module ztw (
    input wire [7:1] i,
    output wire [7:1] z
);
  for (genvar k = 1; k <= 7; ++k) begin : gen_bit
    assign z[k] = (i[k] === 1'bz);
  end
endmodule
