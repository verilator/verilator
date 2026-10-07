// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class item;
  rand int unsigned driver_delay;
endclass

class generic_sequence #(
    type T = item
);
  rand T cmd;
  function new();
    cmd = new;
  endfunction
endclass

module t;
  generic_sequence #(item) seq;
  int result;
  initial begin
    seq = new;
    // Deferred lookup must still report unknown member
    result = seq.randomize() with {bogus_member == 1;};
    `checkd(result, 1);
    $finish;
  end
endmodule
