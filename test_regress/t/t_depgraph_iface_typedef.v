// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

// DESCRIPTION: Verilator: Test for specialized interface typedef fix
//
// This test verifies that when parameterized interfaces are specialized,
// the typedefs within use the correct parameter values, not the template defaults.
// The bug manifests as "Hard packed union members must have equal size" when
// union member widths depend on parameters that aren't properly resolved.

// Parameterized interface with typedefs that depend on the parameter
interface types_if #(parameter int NUM_THREADS = 1)();
  // Union where member sizes depend on parameter
  // If NUM_THREADS=4: raw is 256 bits, data_a is 4x64=256 bits (equal - valid)
  // If NUM_THREADS=1 (default): raw is 64 bits, data_a is 1x64=64 bits (equal - valid)
  // Bug case: If specialized with 4 but typedef uses template default 1,
  // then raw=64 but data_a=256, causing "unequal size" error
  typedef union packed {
    logic [NUM_THREADS*64-1:0] raw;
    logic [NUM_THREADS-1:0][63:0] data_a;
  } data_t;

  // Struct containing the union
  typedef struct packed {
    logic valid;
    data_t d;
  } beat_t;

  // Variable using the typedef - forces width calculation
  beat_t current_beat;
endinterface

module t;
  // Instantiate interface with NUM_THREADS=4
  // The typedefs inside should use NUM_THREADS=4, not the default 1
  types_if #(.NUM_THREADS(4)) types_inst();

  initial begin
    // If compilation succeeds, the union members have equal size
    // which means the parameter was correctly propagated to the typedef
    types_inst.current_beat.valid = 1'b1;
    types_inst.current_beat.d.raw = 256'hDEADBEEF;
    $write("*-* All Coverage Coverage *-*\n");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
