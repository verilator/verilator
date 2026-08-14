// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test that a rand variable used as an index into a non-rand (state) array
// is treated as symbolic in the solver, not folded to a scalar constant.
// This is the standard "pick an unused ID from a pool" idiom: 'used' tracks
// which IDs have already been drawn and is updated by the testbench between
// randomize() calls, not by the solver itself.

class UniqueIdPool;
  rand int id;
  bit used[16];

  constraint c_range { id inside {[0:15]}; }
  constraint c_unused { !used[id]; }
endclass

module t;
  initial begin
    UniqueIdPool obj;
    bit [15:0] seen;
    obj = new;
    seen = '0;
    for (int i = 0; i < 16; i++) begin
      `checkd(obj.randomize(), 1)
      // Each draw must be a legal, not-yet-seen id
      if (obj.id < 0 || obj.id > 15) begin
        $write("%%Error: id out of range: %0d\n", obj.id);
        `stop;
      end
      if (seen[obj.id]) begin
        $write("%%Error: id %0d drawn twice\n", obj.id);
        `stop;
      end
      seen[obj.id] = 1'b1;
      obj.used[obj.id] = 1'b1;
    end
    // All 16 ids must have been drawn exactly once
    `checkd(seen, 16'hffff)
    // Pool is now exhausted -- no legal id remains
    `checkd(obj.randomize(), 0)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
