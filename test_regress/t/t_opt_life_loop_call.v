// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A call inside a loop must invalidate V3Life's tracked knowledge in the loop
// body and every enclosing block. Checks: (A) a local written in the loop body,
// (B) an enclosing constant changed only by the call, (C) a pre-loop assignment
// kept live by the call.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class c;
  int unsigned x;
  int unsigned calls;
  int unsigned v_mem;
  int unsigned sum;

  function void bump();
    calls++;
  endfunction
  function void clobber();
    v_mem = 7;
  endfunction
  function void accum();
    sum += v_mem;
  endfunction

  // A: store to a local inside the loop body must survive.
  function void run_local();
    int unsigned v = 0;
    for (int i = 0; i < 4; i++) begin
      v = 1;
      bump();
    end
    x = v;  // must read 1, not the initializer 0
  endfunction

  // B: constant in the enclosing block, changed only by the call in the loop.
  function void run_enclosing_const();
    v_mem = 5;
    for (int i = 0; i < 4; i++) clobber();
    x = v_mem;  // must read 7, not the pre-loop 5
  endfunction

  // C: pre-loop assignment kept live by a call that reads it.
  function void run_enclosing_del();
    sum = 0;
    v_mem = 5;
    for (int i = 0; i < 4; i++) accum();
    v_mem = 6;  // reassignment must not delete the live v_mem = 5
  endfunction
endclass

module t;
  initial begin
    automatic c o = new();

    o.run_local();
    `checkd(o.x, 1);
    `checkd(o.calls, 4);

    o.run_enclosing_const();
    `checkd(o.x, 7);

    o.run_enclosing_del();
    `checkd(o.sum, 20);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
