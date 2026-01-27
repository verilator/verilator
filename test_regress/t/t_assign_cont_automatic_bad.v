// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  reg g;

  task automatic tsk;
    reg l;
    begin : cont_block
      assign g = signed'(l);  // <--- BAD: using automatic in cont assignment
    end
  endtask

  initial $stop;

endmodule
