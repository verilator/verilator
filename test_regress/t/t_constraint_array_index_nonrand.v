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

// Same, but the rand index is the outer subscript (data[0][idx]) instead of
// the inner one -- reaching the rand base variable through a nested
// ArraySel, not a direct one.
class RandMultidimRandIndexOuter;
  rand int idx;
  rand bit [7:0] data[4][4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[0][idx] == 8'hAA; }
endclass

// Same shape at the exact 2x2 size the regression was originally reported
// at, distinct from the 4x4 case above.
class RandMultidimRandIndexOuterMinimal;
  rand int idx;
  rand bit [7:0] data[2][2];
  constraint c_idx { idx inside {[0:1]}; }
  constraint c_data { data[0][idx] == 8'hAA; }
endclass

// Same, but three dimensions deep with the rand index outermost
// (data[1][2][idx]) -- the array's root must resolve through two nested
// index selects to reach 'data', not just one as in the two-dimensional
// case above.
class RandMultidimRandIndexDeep;
  rand int idx;
  rand bit [7:0] data[4][4][4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[1][2][idx] == 8'hAA; }
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

// An out-of-range idx reads as 0 (IEEE 1800-2023 7.4.2), not as
// used[used.size()-1] -- idx == used.size() is only satisfiable if the
// solver models that default correctly.
class OutOfBoundsIndex;
  rand int idx;
  bit used[3] = '{1, 1, 1};
  constraint c { idx == 3; used[idx] == 0; }
endclass

// Same, but idx runs negative instead of past the top.
class OutOfBoundsIndexNegative;
  rand int idx;
  bit used[3] = '{1, 1, 1};
  constraint c { idx == -1; used[idx] == 0; }
endclass

// Same idea on a non-zero-based declared range, where idx is
// bias-adjusted before comparison -- the default must still apply once
// idx falls outside [1:3], not just outside [0:2].
class OutOfBoundsIndexNonZeroBase;
  rand int idx;
  bit used[1:3] = '{1, 1, 1};
  constraint c { idx == 4; used[idx] == 0; }
endclass

typedef struct {
  bit [7:0] a;
  bit [7:0] b;
} s_t;

// Member select off a constant-indexed struct array, which names the
// element '%s.%s' rather than '(select %s %s)'.
class StructArrayConstIndex;
  rand s_t arr[4];
  constraint c_a { arr[2].a == 8'hBB; }
endclass

module t;
  initial begin
    UniqueIdPool obj;
    UniqueIdPoolViaMember mobj;
    UniqueIdPoolNonZeroBase nzobj;
    UniqueIdPoolDescBase descobj;
    RandArrayRandIndex rand_obj;
    RandMultidimRandIndex mrand_obj;
    RandMultidimRandIndexOuter mrand_outer_obj;
    RandMultidimRandIndexOuterMinimal mrand_outer_min_obj;
    RandMultidimRandIndexDeep mrand_deep_obj;
    RandQueueRandIndex rq_obj;
    StructArrayConstIndex sa_const_obj;
    OutOfBoundsIndex oob_obj;
    OutOfBoundsIndexNegative oob_neg_obj;
    OutOfBoundsIndexNonZeroBase oob_nzb_obj;
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

    mrand_outer_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = mrand_outer_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(mrand_outer_obj.data[0][mrand_outer_obj.idx], 8'hAA);
    end

    mrand_outer_min_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = mrand_outer_min_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(mrand_outer_min_obj.data[0][mrand_outer_min_obj.idx], 8'hAA);
    end

    mrand_deep_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = mrand_deep_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(mrand_deep_obj.data[1][2][mrand_deep_obj.idx], 8'hAA);
    end

    rq_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = rq_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(rq_obj.data[rq_obj.idx], 1'b1);
    end

    sa_const_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = sa_const_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(sa_const_obj.arr[2].a, 8'hBB);
    end

    oob_obj = new;
    randomize_result = oob_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(oob_obj.idx, 3);

    oob_neg_obj = new;
    randomize_result = oob_neg_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(oob_neg_obj.idx, -1);

    oob_nzb_obj = new;
    randomize_result = oob_nzb_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(oob_nzb_obj.idx, 4);

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

    // A rand index into an array that's itself a std::randomize() argument:
    // the argument's own captured copy must stay a symbolic SMT value, the
    // same as a class's own rand member would.
    begin
      bit [7:0] sarr[4];
      int sidx;
      int std_result;
      for (int i = 0; i < 20; i++) begin
        sarr = '{0, 0, 0, 0};
        std_result = std::randomize(sarr, sidx) with {sidx inside {[0 : 3]}; sarr[sidx] == 8'hFF;};
        `checkd(std_result, 1);
        `checkd(sarr[sidx], 8'hFF);
      end
    end

    // Same rand index, but also reaching a plain (non-argument, non-rand)
    // array in the same expression -- that side must still resolve to its
    // own root var and get the non-rand elementwise treatment, not be
    // mistaken for part of the std::randomize() call's own rand set.
    begin
      bit [7:0] sarr2[4];
      bit [7:0] other[4];
      int sidx2;
      int std_result2;
      other = '{8'h11, 8'h22, 8'h33, 8'h44};
      for (int i = 0; i < 20; i++) begin
        sarr2 = '{0, 0, 0, 0};
        std_result2 = std::randomize(
            sarr2, sidx2) with {sidx2 inside {[0 : 3]}; sarr2[sidx2] == other[sidx2];};
        `checkd(std_result2, 1);
        `checkd(sarr2[sidx2], other[sidx2]);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
