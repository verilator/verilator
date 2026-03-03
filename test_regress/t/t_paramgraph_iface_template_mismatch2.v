// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// DESCRIPTION:
// Variant testcase that avoids ASCRANGE by giving the template interface
// a nonzero default, while still detecting template-vs-specialized mixups.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package axi4l;
  typedef struct packed {
    int AddrBits;
    int DataBits;
    int UserBits;
  } cfg_t;
endpackage

interface axi4l_if #(parameter axi4l::cfg_t cfg = '{AddrBits:4, DataBits:16, UserBits:1})();
  typedef logic [cfg.AddrBits-1:0] addr_t;
  typedef logic [cfg.DataBits-1:0] data_t;
  typedef logic [cfg.DataBits/8-1:0] strb_t;
  typedef logic [cfg.UserBits-1:0] user_t;
endinterface

module ccom_to_axi(
  axi4l_if axil_tgt_io
);
  typedef axil_tgt_io.addr_t addr_t;
  typedef axil_tgt_io.data_t data_t;
  typedef axil_tgt_io.strb_t strb_t;

  addr_t addr_q;
  data_t data_q;
  strb_t strb_q;
endmodule

module dummy_consumer(axi4l_if axil_io);
  typedef axil_io.data_t data_t;
  data_t sink;
endmodule

module top;
  localparam axi4l::cfg_t cfg = '{AddrBits:32, DataBits:64, UserBits:2};

  // Live specialized instance used elsewhere.
  axi4l_if #(.cfg(cfg)) axil_live();
  dummy_consumer u_consume(.axil_io(axil_live));

  // Template/default instance used in ccom_to_axi.
  axi4l_if #(cfg) axil_tgt_io();
  ccom_to_axi u_ccom_to_axi(.axil_tgt_io(axil_tgt_io));

  initial begin
    #1;
    `checkd($bits(axil_live.addr_t), 32);
    `checkd($bits(axil_live.data_t), 64);
    `checkd($bits(axil_live.strb_t), 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
