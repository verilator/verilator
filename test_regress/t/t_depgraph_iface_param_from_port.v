// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// DESCRIPTION:
// Regression for interface instances parameterized by interface-port params.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package cfg_pkg;
  typedef struct packed {
    int DataWidth;
    int IdWidth;
  } cfg_t;
endpackage

interface types_if #(parameter cfg_pkg::cfg_t cfg = '0)();
  typedef logic [cfg.DataWidth-1:0] data_t;
  typedef logic [cfg.IdWidth-1:0] id_t;
endinterface

interface bus_if #(parameter cfg_pkg::cfg_t cfg = '0)();
  types_if #(cfg) types();
  typedef types.data_t data_t;
  typedef types.id_t id_t;
endinterface

module child(bus_if io, output int data_w, output int id_w);
  types_if #(io.cfg) port_types();
  typedef port_types.data_t p_data_t;
  typedef port_types.id_t p_id_t;
  assign data_w = $bits(p_data_t);
  assign id_w = $bits(p_id_t);
endmodule

module top;
  localparam cfg_pkg::cfg_t cfg0 = '{DataWidth:32, IdWidth:4};
  localparam cfg_pkg::cfg_t cfg1 = '{DataWidth:64, IdWidth:6};

  bus_if #(cfg0) bus0();
  bus_if #(cfg1) bus1();

  int data_w0;
  int id_w0;
  int data_w1;
  int id_w1;

  child u0(.io(bus0), .data_w(data_w0), .id_w(id_w0));
  child u1(.io(bus1), .data_w(data_w1), .id_w(id_w1));

  initial begin
    #1;
    `checkd(data_w0, 32);
    `checkd(id_w0, 4);
    `checkd(data_w1, 64);
    `checkd(id_w1, 6);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
