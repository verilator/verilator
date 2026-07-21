// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface inf #(int PARAM = 0);
  logic[PARAM-1:0] v;

  modport port_in (
    input v
  );
  modport port_out (
    output v
  );
endinterface

module GenericModule #(PARAM=0) (interface.port_in a);
  localparam int LOC_PARAM = a.PARAM;
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
