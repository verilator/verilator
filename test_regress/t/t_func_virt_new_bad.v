// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
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
    c.f();
  end
endmodule
