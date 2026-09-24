// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface A;
endinterface

typedef virtual A a_t;
typedef a_t a_array_t[6];

class C;
  a_array_t vif;
endclass

module t;
  A b[7] ();
  C c;

  initial begin
    c = new();
    c.vif = b;
  end
endmodule
