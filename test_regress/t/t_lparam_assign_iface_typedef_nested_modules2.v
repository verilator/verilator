// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//     localparam assignment from interface typedef with module
//     hierarchy alongside localparam assignment from interface
//     parameter
//

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface bus_if #(
    parameter int p_awidth = 4,
    parameter int p_dwidth = 7
);
  typedef struct packed {logic [p_awidth-1:0] addr;} rq_t;
  typedef struct packed {logic [p_dwidth-1:0] data;} rs_t;

  rq_t rq;
  rs_t rs;
endinterface

module a_mod (
    bus_if bus_io
);
  localparam bus_rq_t = bus_io.rq_t;
  localparam bus_rs_t = bus_io.rs_t;
  localparam p_awidth = bus_io.p_awidth;
  localparam p_dwidth = bus_io.p_dwidth;

  bus_rq_t rq;
  bus_rs_t rs;

  assign rs.data = 8'ha5;
  assign bus_io.rs = rs;
endmodule

module top ();
  bus_if #(
      .p_awidth(16),
      .p_dwidth(8)
  ) bus_io ();

  a_mod a_mod_inst (.bus_io(bus_io));

  initial begin
    #1;
    `checkh(bus_io.rs.data, 8'ha5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
