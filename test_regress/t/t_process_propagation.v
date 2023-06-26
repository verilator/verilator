// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

event evt1, evt2;

class Foo;
  process p;
  bit event_received;

  function new();
    p = process::self();
  endfunction

  virtual task ewait();
    @evt1 $display("Foo received event `evt1`");
    event_received = 1;
    ->evt2;
  endtask
endclass

class Bar extends Foo;
  function new();
    super.new();
    $display("Constructing Bar");
  endfunction

  virtual task ewait();
    @evt1 $display("Bar received event `evt1`");
    event_received = 1;
  endtask
endclass

module t();
  initial begin
    process p;
    Foo foo;
    Bar bar;

    fork
      begin
        foo = new;
        foo.ewait();
      end
      begin
        bar = new;
        p = process::self();
        bar.ewait();
      end
    join_none

    p.kill();

    ->evt1;

    @evt2 begin
      if (!foo.event_received)
        $stop;
      if (bar.event_received)
        $stop;

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
