// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc #(
    parameter int PARAM = 1
);
  logic [PARAM-1:0] v;
  modport mp(input v);
endinterface

module Leaf #(
    parameter int PARAM = 1
) (
    ifc.mp leaf_a
);
  initial begin
    #1;
    `checkd(leaf_a.PARAM, PARAM);
  end
endmodule

module GenericModule (
    interface.mp a
);
  localparam LOC_PARAM = a.PARAM;
  // A generic interface's parameter, parameterizing a sibling interface cell
  ifc #(.PARAM(LOC_PARAM)) nested_inst ();
  Leaf #(.PARAM(LOC_PARAM)) leaf (nested_inst);
  initial begin
    #1;
    `checkd(a.v, 7);
    `checkd(a.PARAM, 13);
    `checkd(LOC_PARAM, a.PARAM);
  end
endmodule

module t;
  ifc #(.PARAM(13)) inf_inst ();
  GenericModule genericModule (inf_inst);
  initial begin
    inf_inst.v = 7;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
