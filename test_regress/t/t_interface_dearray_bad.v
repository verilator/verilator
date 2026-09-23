// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface A;
endinterface

module sub (
    A p
);
endmodule

typedef virtual A a_t;
typedef a_t a_array_t[6];

class C;
  a_array_t vif;
endclass

module tb_top ();
  A a[6] (), f[6] ();
  C d;

  // Bad: no such instances
  sub s_oob_hi (.p(a[6]));
  sub s_oob_lo (.p(a[-1]));

  initial begin
    a = f;
    a[0:1] = f[0:1];
    a[2] = f[2];

    d = new();

    for (int i = 0; i < 6; ++i) begin
      d.vif[i] = a[i];
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
