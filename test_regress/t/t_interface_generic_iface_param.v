// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface ifc #(
    PARAM
);
  logic [PARAM-1:0] v;
endinterface

module GenericModule (
    interface a
);
  initial begin
    #1;
    if (a.v != 7) $stop;
    if (a.PARAM != 13) $stop;
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
