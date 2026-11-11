// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A default bin cannot be explicitly ignored (IEEE 1800-2023 19.5)

module t;
  covergroup cg with function sample (bit [2:0] value, bit gate);
    cp: coverpoint value {
      bins low = {[0 : 1]};
      ignore_bins others = default;  // <--- Bad
    }
    cp_gated: coverpoint value {
      bins low = {[0 : 1]};
      ignore_bins others[] = default iff (gate);  // <--- Bad
    }
    cp_sequence: coverpoint value {
      bins low = {[0 : 1]};
      ignore_bins others = default sequence;  // <--- Bad
    }
    cp_sequence_gated: coverpoint value {
      bins low = {[0 : 1]};
      ignore_bins others = default sequence iff (gate);  // <--- Bad
    }
  endgroup

  cg inst = new;
endmodule
