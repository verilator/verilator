// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off UNUSEDPARAM

package P;
  typedef struct {
    int depth;
  } memory_config_t;

  typedef struct {
    memory_config_t memory;
    int counters;
  } config_t;
endpackage

module t;
  // A public unpacked-struct parameter is emitted 'static const', so the
  // registration of its members must cast away const like the whole
  // parameter's registration does.
  localparam P::config_t CFG = '{memory: '{depth: 8192}, counters: 6};
  // An unpacked array of structs registers members through a separate path,
  // which used to null-dereference when asking whether it is a literal type.
  localparam P::memory_config_t MEM_ARR[2] = '{'{depth: 16}, '{depth: 32}};

  initial begin
    if (CFG.memory.depth != 8192) $stop;
    if (CFG.counters != 6) $stop;
    // Selected at runtime; indexing an array-of-structs inside a constant
    // expression is a separate, still-unsupported case.
    if (MEM_ARR[1].depth != 32) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
