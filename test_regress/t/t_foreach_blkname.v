// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   function void func();
      int a[2];
      begin
         int t;
      end
      foreach (a[i]) begin
      end
      begin
         int x;
      end
   endfunction
endmodule
