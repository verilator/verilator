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
  // A non-Var/non-GenBlock item the member gather must skip past
  modport mp (input v);
  if (1) begin : blk_decoy
    // Same name as the real parameter below, but not a parameter
    logic PARAM_IF;
  end
  if (1) begin : blk_if
    localparam int PARAM_IF = PARAM + 100;
  end
  for (genvar i = 0; i < 1; i++) begin : blk_for
    localparam int PARAM_FOR = PARAM + 200;
  end
endinterface

module GenericModule (interface.mp a);
  // Two references to the same member, so the second reuses the gathered members
  localparam int LOC_PARAM1 = a.PARAM;
  localparam int LOC_PARAM2 = a.PARAM;
  // Members inside generate blocks, reachable only by recursing into them
  localparam int LOC_IF = a.PARAM_IF;
  localparam int LOC_FOR = a.PARAM_FOR;
  initial begin
    #1;
    `checkd(a.v, 7);
    `checkd(LOC_PARAM1, 13);
    `checkd(LOC_PARAM2, 13);
    `checkd(LOC_IF, 113);
    `checkd(LOC_FOR, 213);
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
