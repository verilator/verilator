// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class c;
   function f();
   endfunction
endclass
module t;
   c cinst;
   initial begin
      cinst = new();
      if(cinst.f) begin end
   end
endmodule
