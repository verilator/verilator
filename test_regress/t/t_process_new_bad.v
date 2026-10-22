// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;
  class process;  // Not std::process, so legal to construct
  endclass
endpackage

module sub;
  class process;  // Not std::process, so legal to construct
  endclass

  initial begin
    automatic process q = new;
  end
endmodule

module t;
  sub u_sub ();

  function automatic void make_in_func();
    std::process sp;
    sp = new;  // <--- Bad: IEEE 1800-2023 9.7
  endfunction

  initial begin
    automatic pkg::process up = new;
    automatic process p = process::self();
    p = new;  // <--- Bad: IEEE 1800-2023 9.7
    make_in_func();
    $stop;
  end
endmodule
