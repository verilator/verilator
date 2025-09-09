// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo #(type T);
  local mailbox #( T ) m;
  function new();
    m = new;
  endfunction
  function bit push( input T t );
    if( m.try_put( t ) != 0 ) begin end
  endfunction
  function int size();
    return m.num();
  endfunction
endclass

class Bar;
  Foo #(int) foo;
  function new();
    foo = new;
  endfunction
  function void send();
    int x;
    if (foo.size() != 0) $stop;
    if (foo.push(x) != 1) begin end
    if (foo.size() != 1) $stop;
  endfunction
endclass

module t;
  initial begin
    Bar bar = new;
    bar.send();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
