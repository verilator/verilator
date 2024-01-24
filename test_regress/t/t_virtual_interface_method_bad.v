// Copyright 2003 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
class ExampleClass;
  localparam NUM_TXNS = 10;
  protected virtual example_if v_if;

  task run();
    v_if.x();
  endtask: run

  function void bind_if(virtual example_if v_if);
    this.v_if = v_if;
  endfunction: bind_if
endclass:  ExampleClass

interface example_if();
  logic      clk;
  logic      rstn;
  logic[7:0] x;
endinterface: example_if

module t(/*AUTOARG*/);

  example_if example_if_inst();

  initial begin: main
    ExampleClass exampleClass = new();

    exampleClass.bind_if(example_if_inst);
    exampleClass.run();
  end: main
endmodule: t
