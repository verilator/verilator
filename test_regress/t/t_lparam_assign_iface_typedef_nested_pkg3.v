// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
//
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package a_pkg;
  typedef struct packed {int unsigned IdBits;} cfg_t;
endpackage

interface bus_if #(
    parameter a_pkg::cfg_t cfg = 0
) ();

  typedef logic [cfg.IdBits-1:0] id_t;
endinterface

module a_mod #(
    parameter int p_expect = 0
) (
    bus_if bus_io
);

  localparam type cfg_id_t = bus_io.id_t;

  cfg_id_t cfg_id;

  initial begin
    #10;
    `checkd($bits(cfg_id), p_expect);
  end

endmodule

module t (
    input logic clk
);
  localparam a_pkg::cfg_t cfg0 = '{IdBits: 5};
  localparam a_pkg::cfg_t cfg1 = '{IdBits: 10};

  bus_if #(.cfg(cfg0)) bus_if0 ();
  bus_if #(.cfg(cfg1)) bus_if1 ();

  a_mod #(5) a_mod0 (.bus_io(bus_if0));

  a_mod #(10) a_mod1 (.bus_io(bus_if1));

  initial begin
    #10;
    #10;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
