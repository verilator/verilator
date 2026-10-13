// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class item;
  rand int unsigned driver_delay;
endclass

class generic_sequence #(type T = item);
  rand T cmd;
  function new();
    cmd = new;
  endfunction
endclass

module t;
  generic_sequence#(item) seq;
  initial begin
    seq = new;
    // 'bogus_member' is in neither the specialized target class nor the
    // caller scope: the deferred post-V3Param lookup must still report it.
    if (seq.randomize() with {
      bogus_member == 1;
    } != 1) $stop;
    $finish;
  end
endmodule
