// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

event evt1, evt2, evt3;

class Foo;
  process p;
  bit event_received;

  function new();
    p = process::self();
  endfunction

  virtual task ewait();
    @evt1 $display("%t: Foo received event `evt1`", $time);
    event_received = 1;
    ->evt2;
  endtask
endclass

class Bar extends Foo;
  function new();
    super.new();
    $display("%t: Constructing Bar", $time);
  endfunction

  virtual task ewait();
    @evt1 $display("%t: Bar received event `evt1`", $time);
    event_received = 1;
  endtask
endclass

export "DPI-C" v_export = task dpi_export;
task dpi_export();
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
      p   = process::self();
      bar.ewait();
    end
  join_none
  #10;
  p.kill();

  ->evt1;
  @evt2 begin
    if (!foo.event_received) $stop;
    if (bar.event_received) $stop;
  end
endtask

import "DPI-C" context task dpi_import();

module t;
  initial begin
    dpi_import();
    if ($time != 10) $stop;
    $display("*-* All Finished *-*\n");
    $finish;
  end
endmodule
