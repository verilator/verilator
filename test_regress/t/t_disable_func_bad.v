// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

int x = 0;

function int increment_x;
  x++;
  return x;
endfunction

function void disable_fork_from_function;
  disable t.init.fork_blk;
endfunction

module t;

  initial begin : init
    fork : fork_blk
      disable_fork_from_function();
    join
    #1 disable increment_x;
  end

endmodule
