// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit [1:0] value;
  bit enabled;

  covergroup cg;
    transitions: coverpoint value {
      bins normal = (0 => 1) iff (enabled);
      ignore_bins ignored = (1 => 2) iff (!enabled);
      illegal_bins illegal = (2 => 3) iff (enabled && value != 0);
    }
    normal_default: coverpoint value {
      bins fallback = default iff (enabled);
    }
    ignored_default: coverpoint value {
      ignore_bins fallback = default iff (!enabled);
    }
    illegal_default: coverpoint value {
      illegal_bins fallback = default iff (enabled && value != 0);
    }
  endgroup

  cg inst = new;
endmodule
