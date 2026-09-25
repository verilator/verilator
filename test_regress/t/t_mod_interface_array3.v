// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Johan Bjork
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface a_if ();
  string s;
endinterface

module sub (
    output string s
);
  initial s = $sformatf("%m");
endmodule

module isub (
    output string s,
    a_if i
);
  initial s = $sformatf("%m");
  initial i.s = $sformatf("%m-iface");
endmodule

// Writes each element of its interface array port
module awrite (
    a_if p[3]
);
  for (genvar k = 0; k < 3; ++k) begin : g
    initial p[k].s = $sformatf("%m");
  end
endmodule

// Passes a slice of its interface array port down
module amid (
    a_if p[4]
);
  awrite i_w (.p(p[1:3]));
endmodule

module pass (
    input [3:0] i,
    output [3:0] o
);
  assign o = i;
endmodule

module usub (
    input logic [3:0] a[4],
    output logic [3:0] o0,
    output logic [3:0] o3
);
  assign o0 = a[0];
  assign o3 = a[3];
endmodule

module rsub (
    ref string r
);
  initial r = $sformatf("%m");
endmodule

module t;

  string str[3:1][1:0];

  a_if iface[3:1][1:0] ();

  isub i_sub[3:1][1:0] (.s(str), .i(iface));

  // Hierarchical references to elements, with genvar indices
  for (genvar a = 1; a < 4; ++a) begin : g_a
    for (genvar b = 0; b < 2; ++b) begin : g_b
      initial begin
        #1;
        `checks(i_sub[a][b].s, $sformatf("t.i_sub[%0d][%0d]", a, b));
      end
    end
  end

  // Negative and non-zero low indices
  string nstr[0:-1][2:1];
  sub i_neg[0:-1][2:1] (.s(nstr));

  // Single element
  string ostr[5:5];
  sub i_one[5:5] (.s(ostr));

  // Vector connection sliced over all dimensions, leftmost element gets the MSBs
  logic [23:0] vin = 24'h543210;
  logic [3:0] vout[1:0][0:2];
  logic [23:0] vcat;
  /* verilator lint_off ASCRANGE */
  pass i_vec[1:0][0:2] (.i(vin), .o(vout));
  pass i_vcat[1:0][0:2] (.i(vin), .o(vcat));
  struct {logic [23:0] f;} vst;
  pass i_vst[1:0][0:2] (.i(vin), .o(vst.f));
  /* verilator lint_on ASCRANGE */

  // Streaming concatenation sliced over the elements
  logic [7:0] sin = 8'hca;
  logic [3:0] sout[1:0];
  pass i_stream[1:0] (.i({<<{sin}}), .o(sout));

  // Instance and connection ranges in opposite directions: connect left to left
  string xstr[2:1][1:3];
  sub i_x[1:2][3:1] (.s(xstr));

  // Ascending instance ranges slicing a vector, leftmost element still gets the MSBs
  logic [3:0] aout[0:1][0:2];
  /* verilator lint_off ASCRANGE */
  pass i_asc[0:1][0:2] (.i(vin), .o(aout));
  /* verilator lint_on ASCRANGE */

  // Unpacked port, connection with the same unpacked dimensions is connected to every element
  logic [3:0] ux[3:0] = '{4'h9, 4'h8, 4'h7, 4'h6};
  logic [3:0] uo0[1:0];
  logic [3:0] uo3[1:0];
  usub i_u[1:0] (.a(ux), .o0(uo0), .o3(uo3));

  // Elements of a module instance array with an interface array port, connected to a
  // two-dimensional interface array, in opposite directions: connect left to left
  a_if i2d[2:1][2:0] ();
  awrite i_aw[1:2] (.p(i2d));

  // One row of a two-dimensional interface array connected to an interface array port
  a_if irow[1:0][0:2] ();
  awrite i_row (.p(irow[1]));

  // A slice of one row of a two-dimensional interface array connected to an interface array
  // port, and an element of one connected to an interface port
  a_if irs[1:0][0:3] ();
  awrite i_rsl (.p(irs[1][1:3]));
  string elstr;
  isub i_el (.s(elstr), .i(irs[0][2]));

  // A slice of an interface array port passed down
  a_if i4[4] ();
  amid i_mid (.p(i4));

  // Ref port connected to an element of an unpacked array
  string rstr[1:0];
  rsub i_ref[1:0] (.r(rstr));

  initial begin
    #2;
    `checks(nstr[0][2], "t.i_neg[0][2]");
    `checks(nstr[0][1], "t.i_neg[0][1]");
    `checks(nstr[-1][2], "t.i_neg[-1][2]");
    `checks(nstr[-1][1], "t.i_neg[-1][1]");
    `checks(i_neg[-1][2].s, "t.i_neg[-1][2]");
    `checks(ostr[5], "t.i_one[5]");
    `checkh(vout[1][0], 4'h5);
    `checkh(vout[1][1], 4'h4);
    `checkh(vout[1][2], 4'h3);
    `checkh(vout[0][0], 4'h2);
    `checkh(vout[0][1], 4'h1);
    `checkh(vout[0][2], 4'h0);
    `checkh(vcat, vin);
    `checkh(vst.f, vin);
    // {<<{8'hca}} is 8'h53
    `checkh(sout[1], 4'h5);
    `checkh(sout[0], 4'h3);
    for (int i = 1; i <= 2; ++i) begin
      for (int j = 1; j <= 3; ++j) begin
        `checks(xstr[i][j], $sformatf("t.i_x[%0d][%0d]", 3 - i, 4 - j));
      end
    end
    `checkh(aout[0][0], 4'h5);
    `checkh(aout[0][1], 4'h4);
    `checkh(aout[0][2], 4'h3);
    `checkh(aout[1][0], 4'h2);
    `checkh(aout[1][1], 4'h1);
    `checkh(aout[1][2], 4'h0);
    // Port a[0] is the leftmost element of the connection, ux[3]
    `checkh(uo0[1], 4'h9);
    `checkh(uo0[0], 4'h9);
    `checkh(uo3[1], 4'h6);
    `checkh(uo3[0], 4'h6);
    // i_aw[1] is the left element, i2d[2]; port element p[0] is the left element, [2]
    `checks(i2d[2][2].s, "t.i_aw[1].g[0]");
    `checks(i2d[2][1].s, "t.i_aw[1].g[1]");
    `checks(i2d[2][0].s, "t.i_aw[1].g[2]");
    `checks(i2d[1][2].s, "t.i_aw[2].g[0]");
    `checks(i2d[1][1].s, "t.i_aw[2].g[1]");
    `checks(i2d[1][0].s, "t.i_aw[2].g[2]");
    `checks(irow[1][0].s, "t.i_row.g[0]");
    `checks(irow[1][1].s, "t.i_row.g[1]");
    `checks(irow[1][2].s, "t.i_row.g[2]");
    `checks(irow[0][0].s, "");
    `checks(irs[1][0].s, "");
    `checks(irs[1][1].s, "t.i_rsl.g[0]");
    `checks(irs[1][2].s, "t.i_rsl.g[1]");
    `checks(irs[1][3].s, "t.i_rsl.g[2]");
    `checks(irs[0][2].s, "t.i_el-iface");
    `checks(irs[0][1].s, "");
    `checks(i4[0].s, "");
    `checks(i4[1].s, "t.i_mid.i_w.g[0]");
    `checks(i4[2].s, "t.i_mid.i_w.g[1]");
    `checks(i4[3].s, "t.i_mid.i_w.g[2]");
    `checks(rstr[1], "t.i_ref[1]");
    `checks(rstr[0], "t.i_ref[0]");
    `checks(str[1][0], "t.i_sub[1][0]");
    `checks(str[1][1], "t.i_sub[1][1]");
    `checks(str[2][0], "t.i_sub[2][0]");
    `checks(str[2][1], "t.i_sub[2][1]");
    `checks(str[3][0], "t.i_sub[3][0]");
    `checks(str[3][1], "t.i_sub[3][1]");
    `checks(iface[1][0].s, "t.i_sub[1][0]-iface");
    `checks(iface[1][1].s, "t.i_sub[1][1]-iface");
    `checks(iface[2][0].s, "t.i_sub[2][0]-iface");
    `checks(iface[2][1].s, "t.i_sub[2][1]-iface");
    `checks(iface[3][0].s, "t.i_sub[3][0]-iface");
    `checks(iface[3][1].s, "t.i_sub[3][1]-iface");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
