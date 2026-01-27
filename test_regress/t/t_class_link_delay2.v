// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pk1;
  typedef struct packed {
    int AddrBits;
    int DataBits;
  } cfg_t;
endpackage

virtual class a_class_t #(
    parameter pk1::cfg_t CFG = 0
);
  // verilator lint_off ASCRANGE
  localparam type addr_t = logic [CFG.AddrBits-1:0];
  localparam type data_t = logic [CFG.DataBits-1:0];
  // verilator lint_on ASCRANGE

  typedef struct packed {
    addr_t addr;
    data_t data;
  } pkt_t;
endclass

interface ifc #(
    parameter pk1::cfg_t CFG = 0
);
  a_class_t #(CFG)::pkt_t p;
endinterface

module a_to_b #(
    parameter pk1::cfg_t ACFG = 0
) (
    ifc bus
);
  // sturf
endmodule

module t;
  localparam pk1::cfg_t ACFG = '{AddrBits : 64, DataBits : 64};

  ifc #(.CFG(ACFG)) the_bus ();

  a_to_b #(ACFG) a_to_b (.bus(the_bus));
endmodule
