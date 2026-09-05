// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 David Garau
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

module GenericModule (
    interface.mp a
);
  // A member that does not exist on the (now concrete) interface
  localparam int LOC_PARAM = a.NONEXISTENT_PARAM;
  initial begin
    #1;
    `checkd(a.v, 7);
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
