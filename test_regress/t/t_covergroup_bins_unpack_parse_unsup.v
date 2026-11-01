// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  covergroup cg_parse_unsup with function sample (bit [3:0] value, bit gate);
    transitions: coverpoint value {
      bins gated[] = (1 => 2) iff (gate);
      ignore_bins ignored_gated = (3 => 4) iff (gate);
      illegal_bins illegal_gated[] = (5 => 6) iff (gate);
      wildcard bins wild = (1 => 2);
      wildcard bins wild_array[] = (1 => 2), (3 => 4) iff (gate);
      wildcard ignore_bins wild_ignored[] = (5 => 6);
      wildcard illegal_bins wild_illegal = (7 => 8) iff (gate);
      bins ranged = ([1 : 2], [3 : 4] => 5);
    }
    defaults: coverpoint value {
      bins gated = default iff (gate);
      ignore_bins ignored_gated[] = default iff (gate);
      illegal_bins illegal_gated[2] = default iff (gate);
      bins sequence_bin = default sequence;
      bins sequence_gated = default sequence iff (gate);
      ignore_bins ignored_sequence = default sequence;
      ignore_bins ignored_sequence_gated = default sequence iff (gate);
      illegal_bins illegal_sequence = default sequence;
      illegal_bins illegal_sequence_gated = default sequence iff (gate);
    }
  endgroup

  cg_parse_unsup parse_cov = new;
endmodule
