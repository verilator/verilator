// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test packed tagged union nested inside unpacked struct (assignment only)

module t;
  // Packed tagged union
  typedef union tagged packed {
    void None;
    logic [7:0] Value;
  } PackedU;

  // Unpacked struct containing packed union
  typedef struct {
    int a;
    PackedU pu;
  } MyStruct;

  // Unpacked tagged union containing struct
  typedef union tagged {
    void Empty;
    MyStruct Data;
  } OuterU;

  OuterU o;

  initial begin
    // Assign nested packed tagged union inside unpacked struct
    o = tagged Data '{a: 42, pu: tagged Value (8'hAB)};

    // Direct field access to verify assignment
    if (o.Data.a != 42) $stop;
    if (o.Data.pu != 9'h1AB) $stop;  // Tag bit 1, value 0xAB

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
