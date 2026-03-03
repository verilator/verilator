// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// DESCRIPTION:
// Minimal testcase to see if unused modules with interface ports
// still trigger ASCRANGE when interface params are defaulted.
//

package axi4;
  typedef struct packed {
    int IdBits;
    int AddrBits;
    int DataBits;
    int UserBits;
  } cfg_t;
endpackage

interface axi4_if #(parameter axi4::cfg_t cfg = '0)();
  typedef logic [cfg.AddrBits-1:0] addr_t;
  typedef logic [cfg.DataBits-1:0] data_t;
  typedef logic [cfg.DataBits/8-1:0] strb_t;
  typedef logic [cfg.UserBits-1:0] user_t;
  typedef logic [cfg.IdBits-1:0] id_t;

  typedef struct packed {
    id_t id;
    addr_t addr;
    user_t user;
  } aw_chan_t;
endinterface

module dead_mod(
  axi4_if axi_io
);
  typedef axi_io.addr_t addr_t;
  typedef axi_io.data_t data_t;
  typedef axi_io.strb_t strb_t;

  addr_t addr_d;
  data_t data_d;
  strb_t strb_d;
endmodule

module dead_top;
  localparam axi4::cfg_t cfg = '{IdBits:4, AddrBits:32, DataBits:64, UserBits:2};
  axi4_if #(.cfg(cfg)) axi_io();

  dead_mod u_dead(.axi_io(axi_io));
endmodule

module top;
  dead_top dead_top();
  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
