// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Cls;
  int x;
  bit b;
  function new;
    x = 10;
  endfunction
  function bit set_x(int a);
    x = a;
    return 1;
  endfunction
  function int get_x;
    return x;
  endfunction
endclass

module t;
  bit dbg = 0;

  initial begin
    Cls cls;
    Cls nullc;
    if (cls != null && cls.x == 10) $stop;
    if (cls != null && cls.get_x() == 10) $stop;
    cls = new;
    if (!cls.set_x(1) || cls.x != 1) $stop;
    if (!cls.set_x(2) || cls.get_x() != 2) $stop;

    // Both '||' guard a member access of a null handle, so both must short circuit.
    // The shared '(nullc == null)' operand and the 32-bit 'nullc.b == 0' compare used
    // to leave a stale entry in V3Const's member-access cache, converting the second
    // '||' to a bitwise Or and dereferencing 'nullc.b' unconditionally.
    dbg = (nullc == null || dbg) && (nullc == null || nullc.b == 0);
    if (dbg !== 1'b1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
