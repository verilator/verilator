// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

event evt1, evt2;

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
    `checkd(foo.event_received, 1);
    `checkd(bar.event_received, 0);
  end
endtask

import "DPI-C" context task dpi_import();

module t;
  initial begin
    dpi_import();
    `checkd($time, 10);
    $display("*-* All Finished *-*\n");
    $finish;
  end
endmodule
