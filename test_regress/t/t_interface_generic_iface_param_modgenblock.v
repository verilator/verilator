// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 David Garau
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface inf #(parameter int PARAM = 1);
  logic [PARAM-1:0] v;
  modport mp (input v);
endinterface

module GenericModule (interface.mp a);
  // Dotted localparam inside a generate block, feeding a sibling cell in the same block.
  // The interface-ref gather must recurse in here yet still find port 'a' at module level.
  // Generate blocks on the interface side are covered by t_interface_generic_iface_param_genblock.
  if (1) begin : blk
    localparam int LOC_PARAM = a.PARAM;
    inf #(.PARAM(LOC_PARAM)) inner();
  end
  initial begin
    #1;
    `checkd(a.v, 7);
    `checkd(blk.LOC_PARAM, 13);
    `checkd(blk.inner.PARAM, 13);
  end
endmodule

module t;
  inf #(.PARAM(13)) inf_inst();
  GenericModule genericModule (inf_inst);
  initial begin
    inf_inst.v = 7;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
