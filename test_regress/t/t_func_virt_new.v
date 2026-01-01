// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class cl #(
    type T = int
);
  function void f();
    T obj = new;
  endfunction
endclass
virtual class vcl;
endclass
;
module t;
  cl #(vcl) c = new;
  initial begin

  end
endmodule
