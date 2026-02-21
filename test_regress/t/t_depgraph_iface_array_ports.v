// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Todd Strader
// SPDX-License-Identifier: CC0-1.0
//
// DESCRIPTION:
// Minimal testcase for depgraph resolution with arrayed interface ports
// and typedefs pulled from interface instances.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package axi_pkg;
  typedef struct packed {
    int IdBits;
    int DataBits;
    int UserBits;
  } cfg_t;
endpackage

interface axi4_if #(parameter axi_pkg::cfg_t cfg = '0)();
  typedef logic [cfg.IdBits-1:0] id_t;
  typedef logic [cfg.DataBits-1:0] data_t;
  typedef logic [cfg.UserBits-1:0] user_t;

  typedef struct packed {
    id_t id;
    data_t data;
    user_t user;
  } req_t;
endinterface

module sink #(parameter int N = 1)(axi4_if tgt_ports [N-1:0]);
  localparam type req_t = tgt_ports[0].req_t;
  req_t rq;
endmodule

module top;
  localparam axi_pkg::cfg_t cfg = '{IdBits:4, DataBits:32, UserBits:2};
  axi4_if #(.cfg(cfg)) tgt_ports [1:0]();

  sink #(.N(2)) u_sink(.tgt_ports(tgt_ports));

  initial begin
    #1;
    `checkd($bits(tgt_ports[0].id_t), 4);
    `checkd($bits(tgt_ports[0].data_t), 32);
    `checkd($bits(tgt_ports[0].user_t), 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
