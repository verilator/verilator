// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Michael Bikovitsky.
// SPDX-License-Identifier: CC0-1.0

module t ();

  wire true1;
  not1 a(true1, '0);

  wire false1;
  not1 b(false1, '1);

  wire true2;
  not1 c(true2, '0);

  wire false2;
  not1 d(false2, '1);

  initial begin
    if (true1 != '1) $stop;
    if (false1 != '0) $stop;
    if (true2 != '1) $stop;
    if (false2 != '0) $stop;
    $finish;
  end

endmodule

primitive not1(q, d);
  output q;
  input d;
  table
    0 : 1;
    1 : 0;
    x : x;
  endtable
endprimitive

primitive not2(q, d);
  output q;
  input d;
  table
    0 : 1;
    1 : 0;
    X : X;
  endtable
endprimitive
