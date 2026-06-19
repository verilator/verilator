// DESCRIPTION: Verilator: Verilog Test module
//
// A class type parameter whose default reads $bits of a sibling type
// parameter must not freeze that sibling at its default width when other
// parameters of the interface are overridden (#7711).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class cls #(
    int width
);
endclass

interface ifc #(
    parameter int width = 8,
    parameter type dtype = logic [width-1:0],
    parameter type cparam = cls#($bits(dtype))
);
  dtype data;
endinterface

module t;
  // width is overridden, dtype keeps its default logic[width-1:0], and the
  // class type parameter is overridden.  dtype must follow width (1 bit).
  ifc #(
      .width(1),
      .cparam(cls #(1))
  ) inst1 ();
  // Same interface left at its default width (8 bits) must still work.
  ifc inst8 ();

  always_comb inst1.data = 1'b0;

  initial begin
    if ($bits(inst1.data) != 1) begin
      $write("%%Error: $bits(inst1.data)=%0d exp=1\n", $bits(inst1.data));
      $stop;
    end
    if ($bits(inst8.data) != 8) begin
      $write("%%Error: $bits(inst8.data)=%0d exp=8\n", $bits(inst8.data));
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
