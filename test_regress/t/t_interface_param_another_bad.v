// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2017 Johan Bjork
// SPDX-License-Identifier: CC0-1.0

module t;
  simple_bus sb_intf ();
  simple_bus #(.PARAMETER(sb_intf.dummy)) simple ();
  required_bus missing ();
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

interface simple_bus #(
    PARAMETER = 0
);
  logic dummy;
endinterface

interface required_bus #(
    type T,
    int W
);
endinterface
