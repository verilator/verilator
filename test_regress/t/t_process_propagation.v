// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

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

module t;
  bit legacy_done, identity_done, kill_done;

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
    #1;
    p.kill();

    ->evt1;

    @evt2 begin
      if (!foo.event_received) $stop;
      if (bar.event_received) $stop;

      legacy_done = 1;
    end
  end

  // The direct call must preserve the caller's process even with a second fork call.
  class Cls;
    static process last;
    static function void record();
      last = process::self();
    endfunction
    static task recordTwice();
      record();
      fork
        record();
      join_none
    endtask
  endclass

  initial begin
    process p;
    p = process::self();
    Cls::recordTwice();
    `checkd(Cls::last == p, 1);
    identity_done = 1;
  end

  class Stopper;
    static task stopChildren();
      disable fork;
    endtask
    static task stopTwice();
      stopChildren();
      fork
        stopChildren();
      join_none
    endtask
  endclass

  initial begin
    int finished;
    finished = 0;
    fork
      #2 finished = 1;
    join_none
    #1 Stopper::stopTwice();
    #2 `checkd(finished, 0);
    kill_done = 1;
  end

  initial begin
    wait (legacy_done && identity_done && kill_done);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
