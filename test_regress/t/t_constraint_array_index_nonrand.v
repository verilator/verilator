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

// Same idiom, but the array is reached through a member select
// (holder.used[id]) rather than a plain variable reference.
class Holder;
  bit used[16];
endclass

class UniqueIdPoolViaMember;
  rand int id;
  Holder holder;

  constraint c_range { id inside {[0:15]}; }
  constraint c_unused { !holder.used[id]; }

  function new();
    holder = new;
  endfunction
endclass

// Same idiom, but the array has a non-zero, non-descending declared range
// ([1:16] instead of the usual [15:0]-equivalent [16]) -- a synthesized
// array-element index has to account for that bias itself.
class UniqueIdPoolNonZeroBase;
  rand int id;
  bit used[1:16];

  constraint c_range { id inside {[1:16]}; }
  constraint c_unused { !used[id]; }
endclass

// A rand array indexed by a rand value already works via a genuine SMT
// array declaration (unaffected by this fix, which only changes the
// non-rand-array case) -- kept here too so this file's own coverage run
// exercises the "array is rand" side of that check, not just the fix.
class RandArrayRandIndex;
  rand int idx;
  rand bit [7:0] data[4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[idx] == 8'hAA; }
endclass

// A rand multidimensional array indexed by a rand value on the outer
// dimension also already works via the same genuine SMT array symbol --
// this exercises the "array is rand but not a supported 1-D shape" side
// of the same check, which a plain 1-D rand array can't reach.
class RandMultidimRandIndex;
  rand int idx;
  rand bit [7:0] data[4][4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[idx][0] == 8'hAA; }
endclass

module t;
  initial begin
    UniqueIdPool obj;
    UniqueIdPoolViaMember mobj;
    UniqueIdPoolNonZeroBase nzobj;
    RandArrayRandIndex rand_obj;
    RandMultidimRandIndex mrand_obj;
    bit [15:0] seen;
    int randomize_result;

    nzobj = new;
    seen = '0;
    for (int i = 0; i < 16; i++) begin
      randomize_result = nzobj.randomize();
      `checkd(randomize_result, 1);
      if (nzobj.id < 1 || nzobj.id > 16) begin
        $write("%%Error: id out of range: %0d\n", nzobj.id);
        `stop;
      end
      if (seen[nzobj.id - 1]) begin
        $write("%%Error: id %0d drawn twice\n", nzobj.id);
        `stop;
      end
      seen[nzobj.id - 1] = 1'b1;
      nzobj.used[nzobj.id] = 1'b1;
    end
    `checkd(seen, 16'hffff);
    randomize_result = nzobj.randomize();
    `checkd(randomize_result, 0);

    rand_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = rand_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(rand_obj.data[rand_obj.idx], 8'hAA);
    end

    mrand_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = mrand_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(mrand_obj.data[mrand_obj.idx][0], 8'hAA);
    end

    mobj = new;
    for (int i = 0; i < 16; i++) begin
      randomize_result = mobj.randomize();
      `checkd(randomize_result, 1);
      if (mobj.id < 0 || mobj.id > 15) begin
        $write("%%Error: id out of range: %0d\n", mobj.id);
        `stop;
      end
      mobj.holder.used[mobj.id] = 1'b1;
    end

    // Repeat the whole draw-all-then-exhaust cycle on a fresh object each
    // time, to guard against solver-randomness flakiness masking a bug.
    repeat (20) begin
      obj = new;
      seen = '0;
      for (int i = 0; i < 16; i++) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
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
      `checkd(seen, 16'hffff);
      // Pool is now exhausted -- no legal id remains
      randomize_result = obj.randomize();
      `checkd(randomize_result, 0);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
