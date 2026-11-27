// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

package types;
  typedef int int_t;
endpackage

package aliases;
  typedef types::int_t int_t;
endpackage

package seqs;
  class seq;
    function int apply_value(aliases::int_t value);
      return value.randomize() with {value < 5;};
    endfunction
  endclass
endpackage

module t;
  seqs::seq seq = new;
  initial $display(seq.apply_value(0));
endmodule
