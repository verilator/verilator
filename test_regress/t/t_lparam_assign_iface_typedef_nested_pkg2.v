// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     assign multiple localparams from interface typedef
//     including nesting.  param dependency.  uses config struct
//     to pass params to module hierarchy and ultimately interface
//

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package a_pkg;
  typedef struct packed {
    int unsigned a_cfg;
    int unsigned b_cfg;
    int unsigned d_cfg;
  } cfg_t;
endpackage

interface z_if #(
    parameter a_pkg::cfg_t CFG = 0
) ();
  typedef struct packed {logic [CFG.d_cfg + CFG.a_cfg - 1:0] data;} req_t;

  logic sig_a;
  logic sig_b;
endinterface

interface y_if #(
    parameter a_pkg::cfg_t CFG = 0
) ();
  typedef struct packed {logic [CFG.a_cfg-1:0] addr;} rq2_t;
endinterface

interface x_if #(
    parameter a_pkg::cfg_t CFG = 0
) ();
  typedef struct packed {logic [CFG.a_cfg-1:0] addr;} rq_t;

  typedef struct packed {logic [CFG.d_cfg-1:0] data;} rs_t;

  y_if #(.CFG(CFG)) y_if0 ();
  z_if #(.CFG(CFG)) z_if0 ();

endinterface

module top ();
  localparam a_pkg::cfg_t CFG = '{a_cfg: 16, b_cfg: 8, d_cfg: 8};

  x_if #(.CFG(CFG)) if0 ();

  localparam type p0_rq2_t = if0.y_if0.rq2_t;
  localparam type p0_rq_t = if0.rq_t;
  localparam type p0_rs_t = if0.rs_t;
  localparam type p0_req_t = if0.z_if0.req_t;

  p0_rq2_t p0_rq2;
  p0_rq_t p0_rq;
  p0_rs_t p0_rs;
  p0_req_t p0_req;

  always_comb begin
    p0_rq2.addr = 16'hcafe;
    p0_rq.addr = 16'hbeef;
    p0_rs.data = 8'h5a;
    p0_req.data = {p0_rq.addr, p0_rs.data};
  end

  initial begin
    #1;
    `checkh(p0_rq2.addr, 16'hcafe);
    `checkh(p0_rq.addr, 16'hbeef);
    `checkh(p0_rs.data, 8'h5a);
    `checkh(p0_req.data, 24'hbeef5a);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
