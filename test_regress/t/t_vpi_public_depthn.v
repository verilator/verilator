// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface AXIS_IF (
             input logic aclk
             );
  logic [127:0] tdata;
  logic [ 31:0] tuser;
  logic tvalid, tready;
  modport master(input aclk, output tdata, tuser, tvalid, input tready);
  modport slave(input aclk, input tdata, tuser, tvalid, output tready);
endinterface : AXIS_IF

module sub (
        input clk,
        AXIS_IF.slave s_axis_if
        );
  assign s_axis_if.tready = s_axis_if.tdata[0];
endmodule

module dut (
        input clk,
        AXIS_IF.slave s_axis_if
        );
  sub u_sub(.*);
endmodule

module t(/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;
  AXIS_IF s_axis_if (.aclk(clk));
  dut u_dut (.clk, .s_axis_if(s_axis_if));
  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
