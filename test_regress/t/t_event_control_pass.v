// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Bar;
  event evt;

  task automatic wait_for_event();
    @evt;
  endtask

  function automatic event get_event();
    return evt;
  endfunction
endclass

class Foo;
  task automatic send_event(Bar b);
    ->b.get_event();
  endtask
endclass

bit got_event;

module t();

  initial begin
    Bar bar;
    Foo foo;
    foo = new;
    bar = new;
    got_event = 0;

    fork
      begin
        bar.wait_for_event();
        $display("Got the event!");
        got_event = 1;
      end
      #10 foo.send_event(bar);
    join

    #99;
    if (!got_event)
      $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
