// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

// Checks that descendants pick up the proper library (IEEE 1800-2023 33.4.1.5)
module sub;
  class C;
    static task info;
      $display("%s.C %%m=%m %%l=%l", `STRINGIFY(m));
    endtask
  endclass
  initial $display("%s %%m=%m %%l=%l", `STRINGIFY(m));
  initial C::info();
endmodule

`define DECL_MODULE(m) \
  module m; \
    sub sub(); \
    initial $display("%s %%m=%m %%l=%l", `STRINGIFY(m)); \
  endmodule

`DECL_MODULE(m10)
`DECL_MODULE(m20)
`DECL_MODULE(m21)
`DECL_MODULE(m22)
`DECL_MODULE(m23)
`DECL_MODULE(m24)
`DECL_MODULE(m30)
`DECL_MODULE(m31)
`DECL_MODULE(m32)
`DECL_MODULE(m40)
`DECL_MODULE(m41)
`DECL_MODULE(m42)
`DECL_MODULE(m43)
