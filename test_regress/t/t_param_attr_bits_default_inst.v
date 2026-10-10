// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// A module instantiated both with and without parameter overrides is used
// directly for the non-overriding instance, while also being the template the
// specialized clone is made from.  $bits() of a type declared in that module
// must still fold to a constant there, as a parameter value may depend on it.

module sub #(
    parameter int W = 1
) ();
  initial if (W != 2) $stop;
endmodule

module mid #(
    parameter int P = 3
) ();
  typedef struct packed {
    logic a;
    logic b;
  } data_t;
  localparam int W2 = $bits(data_t);
  sub #(.W(W2)) i_sub ();
endmodule

module t ();
  // No overrides, so this instance uses the template module itself
  mid #(.P(3)) i_default ();
  // Overrides, so this instance makes the module above a template
  mid #(.P(5)) i_override ();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
