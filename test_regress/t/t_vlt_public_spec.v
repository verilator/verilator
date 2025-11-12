// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module top #(
  parameter int TOP_PARAM = 42
) (
  input   int top_port_i,
  output  int top_port_o
);

  localparam int TOP_LOCALPARAM = 111;
  int top_tmp;

  mid #(.MID_PARM(TOP_PARAM + TOP_LOCALPARAM)) i_mid_0(top_port_i, top_tmp);
  mid #(.MID_PARM(TOP_PARAM + TOP_LOCALPARAM)) i_mid_1(top_tmp, top_port_o);

  function static void f(input int top_f_port_i, output int top_f_port_o);
    localparam int TOP_F_LOCALPARAM = 1;
    top_f_port_o = top_f_port_i + TOP_F_LOCALPARAM;
  endfunction

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module mid #(
  parameter int MID_PARM = 42
) (
  input  int mid_port_i,
  output int mid_port_o
);

  localparam int MID_LOCALPARAM = 11;
  int mid_tmp_a;
  int mid_tmp_b;

  sub #(.SUB_PARAM(MID_PARM + MID_LOCALPARAM)) i_sub_0(mid_port_i, mid_tmp_a);
  assign mid_tmp_b = mid_tmp_a;
  sub #(.SUB_PARAM(MID_PARM + MID_LOCALPARAM)) i_sub_1(mid_tmp_b, mid_port_o);

  function static void f(input int mid_f_port_i, output int mid_f_port_o);
    localparam int MID_F_LOCALPARAM = 1;
    mid_f_port_o = mid_f_port_i + MID_F_LOCALPARAM;
  endfunction

endmodule

module sub #(
  parameter int SUB_PARAM = 42
) (
  input  int sub_port_i,
  output int sub_port_o
);

  localparam int SUB_LOCALPARAM = 1;
  int sub_tmp;

  assign sub_tmp = sub_port_i + SUB_PARAM;
  assign sub_port_o = sub_tmp + SUB_LOCALPARAM;

  function static void f(input int sub_f_port_i, output int sub_f_port_o);
    localparam int SUB_F_LOCALPARAM = 1;
    sub_f_port_o = sub_f_port_i + SUB_F_LOCALPARAM;
  endfunction

endmodule
