// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Todd Strader
// SPDX-License-Identifier: CC0-1.0
//
// DESCRIPTION:
// Minimal testcase for depgraph interface typedef resolution with
// deep interface nesting and specialized parameter overrides.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package acme_pkg;
  typedef struct packed {
    int DataBits;
  } cfg_t;
endpackage

interface acme_types_if #(parameter acme_pkg::cfg_t cfg = '0)();
  typedef logic [cfg.DataBits-1:0] data_t;
endinterface

interface acme_tb_if #(parameter acme_pkg::cfg_t cfg = '0)();
  acme_types_if #(cfg) acme_types();
  typedef acme_types.data_t data_t;
  data_t payload;
endinterface

interface acme_if #(parameter acme_pkg::cfg_t cfg = '0)();
  acme_tb_if #(cfg) rq_tb_io_i();
  acme_types_if #(cfg) acme_types();
  typedef acme_types.data_t data_t;
  data_t passthru;
endinterface

interface acme_wrap_if #(parameter acme_pkg::cfg_t cfg = '0)();
  acme_if #(cfg) acme_io();
  typedef acme_io.data_t data_t;
  data_t leaf;
endinterface

module consumer(acme_wrap_if wrap_io);
  typedef wrap_io.data_t data_t;
  data_t sink;
endmodule

module top;
  localparam acme_pkg::cfg_t cfg0 = '{
    DataBits:64
  };
  localparam acme_pkg::cfg_t cfg1 = '{
    DataBits:128
  };

  acme_wrap_if #(cfg0) wrap0();
  acme_wrap_if #(cfg1) wrap1();

  consumer u_consume0(.wrap_io(wrap0));
  consumer u_consume1(.wrap_io(wrap1));

  initial begin
    #1;
    `checkd($bits(wrap0.data_t), 64);
    `checkd($bits(wrap1.data_t), 128);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
