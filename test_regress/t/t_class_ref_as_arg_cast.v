// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  static task bar(Foo f);
  endtask
endclass

class Qux extends Foo;
endclass

module t;
  initial begin
    Qux qux = new;
    Foo::bar(qux);
    Foo::bar(null);
  end
endmodule
