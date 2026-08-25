// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 David Garau
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface leaf_if;
  localparam int LEAF_PARAM = 42;
  logic dummy;
endinterface

interface ifc #(
    parameter int PARAM = 1
);
  logic [PARAM-1:0] v;
  // Makes 'a.nested.LEAF_PARAM' a chained Dot, whose lhsp is itself a Dot
  leaf_if nested ();
  parameter int ARR[2] = '{PARAM, PARAM + 1};
  modport mp(input v);
endinterface

module GenericModule (
    interface.mp a
);
  localparam int LOC_CHAIN = a.nested.LEAF_PARAM;
  // Makes the Dot's rhsp an indexed select, not a plain identifier
  localparam int LOC_ARR = a.ARR[0];
  initial begin
    #1;
    `checkd(a.v, 7);
    `checkd(LOC_CHAIN, 42);
    `checkd(LOC_ARR, 13);
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
