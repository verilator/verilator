// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface a_if;
  int x;
endinterface

module sub (
    a_if p
);
endmodule

module sub_arr (
    a_if p[2]
);
endmodule

module t;
  virtual a_if vs;
  virtual a_if va[2];

  // Bad: interface ports need interface instances, not virtual interfaces
  sub i_sub (.p(vs));
  sub_arr i_sub_arr (.p(va));
  sub i_subs[2] (.p(va));
endmodule
