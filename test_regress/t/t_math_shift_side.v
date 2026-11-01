// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  int m_n_bits;

  function int get_n_bytes;
    return ((m_n_bits - 1) / 8) + 1;
  endfunction

endclass

module t;

  int i;
  longint q;
  int iq[$];
  longint qq[$];

  initial begin
    Cls c;
    c = new;

    c.m_n_bits = 23;
    if (c.get_n_bytes() != 3) $stop;

    i = 1 << c.get_n_bytes();
    if (i != 8) $stop;

    i = 32'h1234 >> c.get_n_bytes();
    if (i != 32'h246) $stop;

    i = 32'shffffffff >>> c.get_n_bytes();
    if (i != 32'hffffffff) $stop;

    // Oversized constant shift must still evaluate the shifted operand
    iq = '{1, 2, 3};
    i = iq.pop_front() << 8'd40;
    if (i != 0) $stop;
    if (iq.size() != 2) $stop;
    i = iq.pop_front() >> 8'd40;
    if (i != 0) $stop;
    if (iq.size() != 1) $stop;
    qq = '{1, 2};
    q = qq.pop_front() << 8'd70;
    if (q != 0) $stop;
    if (qq.size() != 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
