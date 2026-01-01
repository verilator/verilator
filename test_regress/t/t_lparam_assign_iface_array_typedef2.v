// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package a_pkg;
  typedef struct packed {
    int unsigned IdBits;
  } cfg_t;
endpackage

interface bus_if #(
  parameter a_pkg::cfg_t cfg = 0
)();
  typedef logic [cfg.IdBits-1:0] id_t;
  id_t id;
endinterface

module a_mod #()(
  bus_if bus_tgt_io_a [2]
  ,bus_if bus_mst_io_a [2]
);

  localparam type tgt_id_t = bus_tgt_io_a[0].id_t;
  localparam type mst_id_t = bus_mst_io_a[0].id_t;

  tgt_id_t tgt_id;
  mst_id_t mst_id;

  initial begin
    #10;
    `checkd($bits(tgt_id), 5);
    `checkd($bits(mst_id), 10);
  end

endmodule

module t(
  input logic clk
);
  localparam a_pkg::cfg_t cfg0 = '{IdBits: 5};
  localparam a_pkg::cfg_t cfg1 = '{IdBits: 10};

  bus_if #(.cfg(cfg0)) bus_tgt_io_a [2] ();
  bus_if #(.cfg(cfg1)) bus_mst_io_a [2] ();

  a_mod a_mod0(
    .bus_tgt_io_a(bus_tgt_io_a),
    .bus_mst_io_a(bus_mst_io_a)
  );

  initial begin
    #10;
    #10;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
