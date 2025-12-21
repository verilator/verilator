// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     localparam assignment from interface typedef with module
//     hierarchy.  uses config struct to pass params to module and
//     ultimately interface
//

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package a_pkg;
  typedef struct packed {
    int unsigned awidth;
    int unsigned dwidth;
  } cfg_t;
endpackage

interface bus_if #(
    parameter int p_awidth = 4,
    parameter int p_dwidth = 7
);
  typedef struct packed {logic [p_awidth-1:0] addr;} rq_t;
  typedef struct packed {logic [p_dwidth-1:0] data;} rs_t;

  rq_t rq;
  rs_t rs;
endinterface

module a_mod #(
    parameter a_pkg::cfg_t cfg = 0
) (
    bus_if bus_io
);
  localparam bus_rq_t = bus_io.rq_t;
  localparam bus_rs_t = bus_io.rs_t;

  bus_rq_t rq;
  bus_rs_t rs;

  assign rq = bus_io.rq;
  assign bus_io.rs = rs;

  always_comb begin
    rs.data = 8'ha5;
  end
endmodule

module top ();
  localparam a_pkg::cfg_t cfg = '{awidth : 16, dwidth : 8};
  bus_if #(
      .p_awidth(16),
      .p_dwidth(8)
  ) bus_io ();

  a_mod #(cfg) a_mod_inst (.bus_io(bus_io));

  initial begin
    #1;
    `checkh(bus_io.rs.data, 8'ha5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
