// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inf #(parameter int PARAM = 1);
  logic [PARAM-1:0] v;
  modport mp (input v);
endinterface

module Leaf #(parameter int PARAM = 1) (inf.mp leaf_a);
  initial begin
    #1;
    if (leaf_a.PARAM != PARAM) $stop;
  end
endmodule

module GenericModule (interface.mp a);
  localparam LOC_PARAM = a.PARAM;
  // A localparam derived from a generic interface's parameter, used to
  // parameterize a sibling interface cell instantiated in this same module.
  inf #(.PARAM(LOC_PARAM)) nested_inst();
  Leaf #(.PARAM(LOC_PARAM)) leaf (nested_inst);
  initial begin
    #1;
    if (a.v != 7) $stop;
    if (a.PARAM != 13) $stop;
    if (LOC_PARAM != a.PARAM) $stop;
  end
endmodule

module t;
  inf  #(.PARAM(13)) inf_inst();
  GenericModule genericModule (inf_inst);
  initial begin
    inf_inst.v = 7;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
