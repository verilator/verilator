// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module test;
  typedef enum { FOO_0 } foo_e;
  typedef enum { BAR_0 } bar_e;

  class baz #(parameter type E = foo_e);
    static function void print();
      E enum_item;
      if (enum_item.first().name() != "BAR_0")
        $stop;
    endfunction
    class Inner1;
      static function void print();
        E enum_item;
        if (enum_item.first().name() != "BAR_0")
          $stop;
      endfunction
    endclass
  endclass

  initial begin
    baz#(bar_e)::print();
    baz#(bar_e)::Inner1::print();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
