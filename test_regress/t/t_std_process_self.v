// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  static task do_something();
`ifdef USE_STD_PREFIX
    std::process p;
`else
    process p;
`endif
    p = process::self();
  endtask
endclass

module t();
  initial begin
    Foo::do_something();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
