// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface inf #(parameter int PARAM = 1);
  logic [PARAM-1:0] v;
endinterface

module leaf (interface d);
  initial begin
    #1;
    `checkd(d.v, 13);
    `checkd(d.PARAM, 5);
  end
endmodule

module mid2 (interface c);
  leaf leaf_i(.d(c));
endmodule

module mid1 (interface b);
  mid2 mid2_i(.c(b));
endmodule

module t;
  inf #(.PARAM(5)) a();
  mid1 mid1_i(.b(a));
  initial begin
    a.v = 13;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
