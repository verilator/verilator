// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface ifc;
  integer i;
endinterface

module sub (
    interface i
);
  logic not_ifc;
  typedef i.not_found_t choice_t;  // <--- Error: not found typedef
endmodule

module t;
  ifc u_ifc ();
  sub u_sub (u_ifc);
endmodule
