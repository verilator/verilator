// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// The invalid break exits after LinkJump handles the shadowed disable target.

module t;

  initial begin : blk
    fork
    join
  end

  initial fork : caller
    begin : blk
      disable t.blk;
      break;
    end
  join
endmodule
