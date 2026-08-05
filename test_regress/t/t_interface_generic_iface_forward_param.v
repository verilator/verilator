// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface inf #(parameter int PARAM = 1);
  logic [PARAM-1:0] v;
endinterface

module leaf (inf c);
  initial begin
    #1;
    `checkd(c.v, 13)
    `checkd(c.PARAM, 5)
  end
endmodule

module mid #(int PARAM = 1)  (interface b);
  leaf leaf_i(.c(b));
  initial `checkd(PARAM,7)
endmodule

module t;
  inf #(.PARAM(5)) a();
  mid #(.PARAM(7)) mid_i (.b(a));
  initial begin
    a.v = 13;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
