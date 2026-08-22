// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test the "pick an unused ID from a pool" idiom: a rand index into a
// non-rand array must stay symbolic in the solver, not fold to a constant.

class UniqueIdPool;
  rand int id;
  bit used[16];

  constraint c_range { id inside {[0:15]}; }
  constraint c_unused { !used[id]; }
endclass

// Same idiom, reached via a member select (holder.used[id]).
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

// Same idiom, but 'used' has a non-zero declared range ([1:16]).
class UniqueIdPoolNonZeroBase;
  rand int id;
  bit used[1:16];

  constraint c_range { id inside {[1:16]}; }
  constraint c_unused { !used[id]; }
endclass

// Same, but the declared range runs the opposite direction ([16:1]).
class UniqueIdPoolDescBase;
  rand int id;
  bit used[16:1];

  constraint c_range { id inside {[1:16]}; }
  constraint c_unused { !used[id]; }
endclass

// A rand array indexed by a rand value: unaffected by this fix, kept
// here for coverage of the "array is rand" path.
class RandArrayRandIndex;
  rand int idx;
  rand bit [7:0] data[4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[idx] == 8'hAA; }
endclass

// Same, but 'data' is multidimensional.
class RandMultidimRandIndex;
  rand int idx;
  rand bit [7:0] data[4][4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[idx][0] == 8'hAA; }
endclass

// Same idiom again, but the rand array is a queue directly rather than a
// fixed array.
class RandQueueRandIndex;
  rand bit data[$];
  rand int idx;
  constraint c_size { data.size() == 4; }
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[idx] == 1; }
endclass

module t;
  initial begin
    UniqueIdPool obj;
    UniqueIdPoolViaMember mobj;
    UniqueIdPoolNonZeroBase nzobj;
    UniqueIdPoolDescBase descobj;
    RandArrayRandIndex rand_obj;
    RandMultidimRandIndex mrand_obj;
    RandQueueRandIndex rq_obj;
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

    descobj = new;
    seen = '0;
    for (int i = 0; i < 16; i++) begin
      randomize_result = descobj.randomize();
      `checkd(randomize_result, 1);
      if (descobj.id < 1 || descobj.id > 16) begin
        $write("%%Error: id out of range: %0d\n", descobj.id);
        `stop;
      end
      if (seen[descobj.id - 1]) begin
        $write("%%Error: id %0d drawn twice\n", descobj.id);
        `stop;
      end
      seen[descobj.id - 1] = 1'b1;
      descobj.used[descobj.id] = 1'b1;
    end
    `checkd(seen, 16'hffff);
    randomize_result = descobj.randomize();
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

    rq_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = rq_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(rq_obj.data[rq_obj.idx], 1'b1);
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
