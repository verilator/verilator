// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

package pkg;
  typedef struct {
    bit [17:0] foo;
    bit [13:0] bar;
  } Bar;
endpackage

interface iface;
  bit [13:0] foo;
  modport in (input foo);
  modport out (output foo);
endinterface

class Foo;
  task test(logic x, bit y, bit z);
    if (x !== 'z) $stop;
    if (y !== 0) $stop;
    if (z !== 0) $stop;
  endtask

  function bit foo(bit z);
    if (!z) $stop;
    return z;
  endfunction

  function bit bar(logic x, bit y, bit z);
    return x || !y || z || (foo(z) || foo(z));
  endfunction

  function logic bar4(logic x, bit y, bit z);
    return x || y || !(foo(z) || foo(z));
  endfunction
endclass

module m(input int val, output bit ok);
  always_comb begin
    case (val)
      3: ok = 1;
      default: ok = 0;
    endcase
  end
endmodule

module t;
  import pkg::Bar;

  wire [17:0] constWire = 18'hd;
  string testStr = "Hellp";
  static integer t = int'($time);
  logic ok;
  m m(t, ok);
  iface iface_inst();

  initial begin
    static Foo foo = new;
    static Bar bar;
    static int i;

    if (t !== 0) $stop;
    bar.foo = constWire;
    bar.bar = 14;
    if (bar.foo !== 13) $stop;
    if (bar.bar !== 14) $stop;
    void'($urandom);

    testStr.putc(4, "o");
    if (testStr != "Hello") $stop;
    testStr.putc(4, "3");
    $sscanf(testStr, "Hell%d", i);
    if (i !== 3) $stop;
    t = i;

    foo.test('z, 'z, 0);
    if (foo.bar('z, 'z, 0) !== 1) $stop;
    assert (foo.bar4('z, 'z, 1) === 'x) i = 7;
    else $stop;

    if (i !== 7) $stop;
    #1 if (ok !== 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
