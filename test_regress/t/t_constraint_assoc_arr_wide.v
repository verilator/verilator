// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class AssocIntegralWide;

  rand bit [31:0] assoc_array[bit[64:0]];
  rand bit [31:0] assoc_array_128[bit[128:0]];
  rand bit [31:0] assoc_array_2d[bit[64:0]][bit[128:0]];

  constraint valid_entries {
      assoc_array[65'd6] == 32'd8;
      assoc_array[65'h1FFFFFFFFFFFFFFFF] == 32'hDEADBEEF;

      assoc_array_128[129'd6] == 32'd16;
      assoc_array_128[129'h1FFFFFFFFFFFFFFFFFFFFFFFF] == 32'hCAFEBABE;

      assoc_array_2d[65'd6][129'd6] == 32'd32;
      assoc_array_2d[65'h1FFFFFFFFFFFFFFFF][129'h1FFFFFFFFFFFFFFFFFFFFFFFF] == 32'hBADF00D;
  }

  // Constructor to initialize arrays
  function new();
    assoc_array[65'd0] = 32'd0;
    assoc_array[65'd6] = 32'd0;
    assoc_array[65'h1FFFFFFFFFFFFFFFF] = 32'd0;

    assoc_array_128[129'd0] = 32'd0;
    assoc_array_128[129'd6] = 32'd0;
    assoc_array_128[129'h1FFFFFFFFFFFFFFFFFFFFFFFF] = 32'd0;

    assoc_array_2d[65'd6][129'd6] = 32'd0;
    assoc_array_2d[65'h1FFFFFFFFFFFFFFFF][129'h1FFFFFFFFFFFFFFFFFFFFFFFF] = 32'd0;
  endfunction

  // Self-check function to verify constraints
  function void self_check();
    if (assoc_array[65'd6] != 32'd8)
      $stop;
    if (assoc_array[65'h1FFFFFFFFFFFFFFFF] != 32'hDEADBEEF)
      $stop;

    if (assoc_array_128[129'd6] != 32'd16)
      $stop;
    if (assoc_array_128[129'h1FFFFFFFFFFFFFFFFFFFFFFFF] != 32'hCAFEBABE)
      $stop;

    if (assoc_array_2d[65'd6][129'd6] != 32'd32)
      $stop;
    if (assoc_array_2d[65'h1FFFFFFFFFFFFFFFF][129'h1FFFFFFFFFFFFFFFFFFFFFFFF] != 32'hBADF00D)
      $stop;
  endfunction

endclass

class AssocStringWide;

  rand bit [31:0] array_32[string];
  rand bit [31:0] array_64[string];
  rand bit [31:0] array_96[string];
  rand bit [31:0] array_128[string];

  constraint valid_entries {
    // <= 32 bits
    array_32["pv"] == 32'd10;
    // > 32 and <= 64 bits
    array_64["verilog"] == 32'd20;
    // > 32 and <= 64 bits
    array_96["verilator"] == 32'd30;
    // > 64 and <= 96 bits
    array_128["systemverilog"] == 32'd40;
  }

  function new();
    array_32["pv"] = 32'd0;
    array_64["verilog"] = 32'd0;
    array_96["verilator"] = 32'd0;
    array_128["systemverilog"] = 32'd0;
  endfunction

  function void self_check();
    if (array_32["pv"] != 32'd10) $stop;
    if (array_64["verilog"] != 32'd20) $stop;
    if (array_96["verilator"] != 32'd30) $stop;
    if (array_128["systemverilog"] != 32'd40) $stop;
  endfunction

endclass


module t_constraint_assoc_arr_wide;

  AssocIntegralWide integral_wide;
  AssocStringWide string_wide;

  int success;
  initial begin

    integral_wide = new();
    string_wide = new();

    success = integral_wide.randomize();
    if (success != 1) $stop;
    integral_wide.self_check();

    success = string_wide.randomize();
    if (success != 1) $stop;
    string_wide.self_check();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
