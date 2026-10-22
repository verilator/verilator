// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;
  function void f();
  endfunction
endpackage

function void g();
endfunction

module t;
  import pkg::*;
  // Bad: defined in the package, not in this module
  export "DPI-C" function f;
  // Bad: defined in $unit, not in this module
  export "DPI-C" function g;

  function void h();
  endfunction
  if (1) begin : gen
    // Bad: defined in the module, not in this generate block
    export "DPI-C" function h;
  end
endmodule
