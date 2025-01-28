// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface iface #(parameter DWIDTH = 32)();
  localparam TOTAL_PACKED_WIDTH = DWIDTH + 1;
  modport Tx(output sop, data, import unpack);
  logic sop;
  logic [DWIDTH - 1:0]  data = '0;

  task static unpack(input logic [TOTAL_PACKED_WIDTH-1:0] packed_in, input logic sop_i);
    logic sop_nc;
    {data, sop_nc} <= packed_in;
    sop <= sop_i;
  endtask
endinterface

module t;
iface ifc();
endmodule
