// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ifc;
  integer i;
endinterface

module sub (
    interface i
);
  logic not_ifc;
  typedef not_found.choice_t choice1_t;  // <--- Error: not found interface port
  typedef i.not_found_t choice2_t;  // <--- Error: not found typedef
  typedef not_ifc.x_t choice3_t;  // <--- Error: sub not interface reference
endmodule

module t;
  ifc u_ifc ();
  sub u_sub (u_ifc);
endmodule
