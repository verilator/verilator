// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// DESCRIPTION:
// Combined test mixing PIN-assigned type param interface (t_interface_derived_type)
// with nested captured typedef/localparam (t_lparam_dep_iface6).

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

typedef struct packed {
  int unsigned ABits;
  int unsigned BBits;
} scp_cfg_t;

interface a_if #(parameter a_p = 0)();
  localparam int LP0 = a_p;
  typedef logic [LP0-1:0] a_t;
endinterface

interface sct_if #(parameter scp_cfg_t cfg = 0)();
  localparam int LP0 = cfg.ABits * cfg.BBits;
  a_if #(LP0) a_if0();
  typedef a_if0.a_t a_t;
endinterface

interface sc_if #(parameter scp_cfg_t cfg = 0)();
  sct_if #(cfg) types();
  typedef types.a_t a_t;
endinterface

interface intf #(
  parameter type data_t = bit,
  parameter int arr[2][4]
) ();
  data_t data;
  logic [$bits(data)-1:0] other_data;
endinterface

module sub #(
  parameter int width,
  parameter int arr[2][4]
) ();
  typedef struct packed {
      logic [3:3] [0:0] [width-1:0] field;
  } user_type_t;

  intf #(
      .data_t(user_type_t),
      .arr(arr)
  ) the_intf ();

  logic [width-1:0] signal;

  always_comb begin
      the_intf.data.field = signal;
      the_intf.other_data = signal;
  end
endmodule

module sc #(parameter scp_cfg_t cfg=0) (
  sc_if io
);
  typedef io.a_t a_t;

  initial begin
    #1;
    `checkd($bits(a_t), 6);
  end
endmodule

module t (input clk);
  localparam scp_cfg_t sc_cfg = '{ABits: 2, BBits: 3};

  sc_if #(sc_cfg) sc_io ();
  sc #(sc_cfg) sc_inst (.io(sc_io));

  sub #(.width(8), .arr('{'{8, 2, 3, 4}, '{1, 2, 3, 4}})) sub8 ();

  typedef sc_io.types.a_if0.a_t inner_t;
  typedef sc_io.types.a_t mid_t;

  initial begin
    #1;
    `checkd($bits(inner_t), 6);
    `checkd($bits(mid_t), 6);
    `checkd($bits(sub8.the_intf.data), 8);

    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
