// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A parameter whose default is a cast of a member of a struct-typed
// parameter.  

typedef struct packed {int unsigned CAP;} cfg_t;

module m #(
  parameter cfg_t cfg = '{CAP: 0},
  parameter int unsigned p_cap = int'(cfg.CAP)
);
endmodule

module t;
  localparam cfg_t c = '{CAP: 32};

  m #(.cfg(c), .p_cap(64)) u_over ();  // explicit override, elaborated first
  m #(.cfg(c)) u_dflt ();  // takes the default: int'(cfg.CAP) == 32

  initial begin
    `checkd(u_over.p_cap, 64);
    `checkd(u_dflt.p_cap, 32);  // 0 before the fix
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
