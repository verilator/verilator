// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg1;
  parameter p1 = 1;
  localparam p2 = 2;
  typedef logic [1:0] word;
  word v;
  event e;
  function automatic word f(word g);
    return g + 1;
  endfunction
  task automatic h(word i);
    v = v + i;
  endtask
endpackage

package pkg2;
  parameter p1 = 1;
  localparam p2 = 2;
  typedef logic [1:0] word;
  word v;
  event e;
  function automatic word f(word g);
    return g + 1;
  endfunction
  task automatic h(word i);
    v = v + i;
  endtask
  localparam ONLY2 = 3;
endpackage

package pkg3;
  import pkg2::*;
  export pkg2::ONLY2;
endpackage

module t;
  import pkg1::*;
  import pkg2::*;
  import pkg3::*;

  word my_v;  // <--- Error: ambiguous
  int ok = ONLY2;  // Same declaration through pkg2 and pkg3 is not ambiguous

  initial begin
    int p1;  // Local declaration hides the wildcard imports
    p1 = 1;
    @(e) v = p1 + p2;  // <--- Error: e, v, p2 ambiguous
    h(f(1));  // <--- Error: h, f ambiguous
  end
endmodule
