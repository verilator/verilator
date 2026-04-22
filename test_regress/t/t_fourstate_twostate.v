// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Foo;
  task test(logic x, bit y, bit z);
    if (x !== 'z) $stop;
    if (y !== 0) $stop;
    if (z !== 0) $stop;
  endtask

  function bit foo(bit z);
    if (!z) $stop;
    return 0;
  endfunction

  function bit bar(logic x, bit y, bit z);
    return x || !y || z || (foo(z) || foo(z));
  endfunction
endclass

module t;
  initial begin
    static Foo foo = new;
    foo.test('z, 'z, 0);
    if (foo.bar('z, 'z, 0) !== 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
