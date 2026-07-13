// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Inlined automatic function leaves CReset in always_comb: fold bails, retain.
interface swap_if #(
  parameter int DBW = 8
) ();
  logic [DBW-1:0][7:0] wdata;
  logic [DBW-1:0][7:0] swapped;

  function automatic logic [DBW-1:0][7:0] swap_endianness(logic [DBW-1:0][7:0] input_value);
    integer i;
    logic [DBW-1:0][7:0] input_value_swapped;
    for (i = 0; i < DBW; i++) input_value_swapped[DBW - 1 - i] = input_value[i];
    return input_value_swapped;
  endfunction

  modport slave(input wdata, output swapped, import swap_endianness);
endinterface

module sub (swap_if.slave s);
  // Inlined function introduces CReset into combinational block.
  always_comb s.swapped = s.swap_endianness(s.wdata);
endmodule

module t (
  input logic clk,
  input logic [7:0][7:0] d,
  output logic [7:0][7:0] o
);
  swap_if #(.DBW(8)) intf ();
  assign intf.wdata = d;
  assign o = intf.swapped;
  sub u (intf);
endmodule
