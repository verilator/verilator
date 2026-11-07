// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
`define check_calls(obj, cond) \
  repeat (16) begin \
    automatic int randomize_result = obj.randomize(); \
    `checkd(randomize_result, 1); \
    `checkd(cond, 1'b1); \
  end
// verilog_format: on

// Test that rand variables used as array indices in constraints are treated
// as symbolic in the solver, not evaluated at C++ constraint setup time.

class RandArrayIndexTest;
  rand bit [1:0] idx;
  rand bit [7:0] data [4];
  rand bit [7:0] selected_value;

  constraint solve_order { solve idx before selected_value; }
  constraint value_match { selected_value == data[idx]; }
  constraint data_values {
    foreach (data[i]) {
      data[i] inside {[8'd10:8'd50]};
    }
  }
endclass

module t;
  initial begin
    int randomize_result;
    static RandArrayIndexTest obj = new();
    repeat (20) begin
      randomize_result = obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(obj.selected_value, obj.data[obj.idx]);
      `check_range(obj.selected_value, 8'd10, 8'd50)
    end
  end

  // The rest index a state array, which has no solver variable to select from

  class RandIndex;
    rand bit [1:0] c;
    rand bit [3:0] x;
    bit [1:0] a[4] = '{1, 1, 0, 0};
    constraint k {
      a[c] == 1;
      x > 0;
    }
  endclass

  initial begin
    automatic RandIndex o = new;
    automatic int randomize_result;
    `check_calls(o, o.a[o.c] == 1);
    // The array is read at each randomize()
    o.a = '{0, 0, 1, 1};
    `check_calls(o, o.c >= 2);
    // A frozen index keeps its value, so the array only checks it
    o.c = 3;
    o.c.rand_mode(0);
    randomize_result = o.randomize();
    `checkd(randomize_result, 1);
    `checkd(o.c, 3);
    o.c = 0;
    randomize_result = o.randomize();
    `checkd(randomize_result, 0);
  end

  class RandcIndex;
    randc bit [1:0] c;
    rand bit [3:0] x;
    bit [1:0] a[4] = '{1, 1, 0, 0};
    constraint k {
      a[c] == 1;
      x > 0;
    }
  endclass

  initial begin
    automatic RandcIndex o = new;
    automatic int count[4] = '{default: 0};
    // The two feasible values still cycle
    repeat (8) begin
      automatic int randomize_result = o.randomize();
      `checkd(randomize_result, 1);
      ++count[o.c];
    end
    `checkd(count[0], 4);
    `checkd(count[1], 4);
  end

  // A std::randomize() argument as the index
  initial begin
    automatic bit [1:0] a[4] = '{1, 1, 0, 0};
    automatic bit [1:0] c;
    repeat (16) begin
      automatic int randomize_result = std::randomize(c) with {a[c] == 1;};
      `checkd(randomize_result, 1);
      `checkd(a[c], 1);
    end
  end

  class Bounds;
    randc bit [2:0] c;
    bit [1:0] a[1:4] = '{1, 0, 1, 0};
    constraint k {
      c >= 1;
      c <= 4;
      a[c] == 1;
    }
  endclass

  initial begin
    automatic Bounds o = new;
    `check_calls(o, o.a[o.c] == 1);
  end

  class Descending;
    randc bit [1:0] c;
    bit [1:0] a[3:0] = '{1, 1, 0, 0};
    constraint k {a[c] == 1;}
  endclass

  initial begin
    automatic Descending o = new;
    `check_calls(o, o.a[o.c] == 1);
  end

  class Expression;
    randc bit [1:0] c;
    bit [1:0] a[4] = '{1, 1, 0, 0};
    constraint k {a[3-c] == 1;}
  endclass

  initial begin
    automatic Expression o = new;
    `check_calls(o, o.a[3-o.c] == 1);
  end

  class InnerArray;
    randc bit [1:0] c;
    bit [1:0] a[4] = '{1, 1, 0, 0};
    bit [1:0] b[4] = '{2, 3, 0, 1};
    constraint k {a[b[c]] == 1;}
  endclass

  initial begin
    automatic InnerArray o = new;
    `check_calls(o, o.a[o.b[o.c]] == 1);
  end

  class RowOfState;
    randc bit [1:0] c;
    bit [1:0] a[2][4] = '{'{0, 0, 0, 0}, '{1, 1, 0, 0}};
    constraint k {a[1][c] == 1;}
  endclass

  initial begin
    automatic RowOfState o = new;
    `check_calls(o, o.a[1][o.c] == 1);
  end

  class Holder;
    bit [1:0] a[4] = '{1, 1, 0, 0};
  endclass

  class Member;
    randc bit [1:0] c;
    Holder h = new;
    constraint k {h.a[c] == 1;}
  endclass

  initial begin
    automatic Member o = new;
    `check_calls(o, o.h.a[o.c] == 1);
  end

  class RandElement;
    randc bit [1:0] c;
    rand bit [1:0] v[2];
    bit [1:0] a[4] = '{1, 2, 1, 2};
    constraint k {a[c] == v[0];}
  endclass

  initial begin
    automatic RandElement o = new;
    `check_calls(o, o.a[o.c] == o.v[0]);
  end

  class WideElement;
    randc bit [1:0] c;
    bit [69:0] a[4] = '{70'h1, 70'h20000000000000001, 70'h0, 70'h0};
    constraint k {a[c] == 70'h1;}
  endclass

  initial begin
    automatic WideElement o = new;
    `check_calls(o, o.a[o.c] == 70'h1);
  end

  // An index wider than the array is cut to the bits addressing it, as for any read of a[c]
  // verilator lint_off WIDTHTRUNC
  class Index7Element15;
    randc bit [6:0] c;
    bit [14:0] a[9] = '{0, 0, 15'h5ab5, 0, 0, 15'h5ab5, 0, 0, 0};
    constraint k {a[c] == 15'h5ab5;}
  endclass

  initial begin
    automatic Index7Element15 o = new;
    `check_calls(o, o.a[o.c] == 15'h5ab5);
  end

  class Index15Element7;
    rand bit [14:0] c;
    bit [6:0] a[7] = '{0, 7'h55, 0, 0, 0, 7'h55, 0};
    constraint k {a[c] == 7'h55;}
  endclass

  initial begin
    automatic Index15Element7 o = new;
    `check_calls(o, o.a[o.c] == 7'h55);
  end

  class Index33;
    rand bit [32:0] c;
    bit [6:0] a[5] = '{0, 0, 7'h55, 0, 0};
    constraint k {a[c] == 7'h55;}
  endclass

  initial begin
    automatic Index33 o = new;
    `check_calls(o, o.a[o.c] == 7'h55);
  end
  // verilator lint_on WIDTHTRUNC

  class IntIndex;
    rand int c;
    bit [6:0] a[5] = '{0, 0, 7'h55, 0, 0};
    constraint k {a[c] == 7'h55;}
  endclass

  initial begin
    automatic IntIndex o = new;
    `check_calls(o, o.a[o.c] == 7'h55);
  end

  typedef bit [6:0] arr_t[5];

  class TypedefArray;
    rand bit [2:0] c;
    arr_t a = '{7'h11, 7'h55, 7'h22, 7'h55, 7'h33};
    constraint k {a[c] == 7'h55;}
  endclass

  initial begin
    automatic TypedefArray o = new;
    `check_calls(o, o.c == 1 || o.c == 3);
  end

  // Three elements: an index of 3 is out of range and reads as zero
  class OutOfRange;
    randc bit [1:0] c;
    bit [1:0] a[3] = '{1, 1, 1};
    constraint k {a[c] == 0;}
  endclass

  initial begin
    automatic OutOfRange o = new;
    `check_calls(o, o.c == 3);
  end

  // More elements than a 3-bit index can address: the last two are never chosen
  class NarrowIndex;
    rand bit [2:0] c;
    bit [6:0] want;
    bit [6:0] a[10] = '{1, 0, 33, 0, 0, 0, 33, 0, 33, 44};
    // verilator lint_off WIDTHEXPAND
    constraint k {a[c] == want;}
    // verilator lint_on WIDTHEXPAND
  endclass

  initial begin
    automatic NarrowIndex o = new;
    automatic int count[8] = '{default: 0};
    automatic int randomize_result;
    o.want = 33;
    repeat (64) begin
      randomize_result = o.randomize();
      `checkd(randomize_result, 1);
      ++count[o.c];
    end
    `checkd(count[2] + count[6], 64);
    `checkd(count[2] > 0, 1'b1);
    `checkd(count[6] > 0, 1'b1);
    o.want = 44;
    randomize_result = o.randomize();
    `checkd(randomize_result, 0);
  end

  // Not compared position by position, so these must still build when turned off
  class NotCompared;
    rand bit [1:0] c;
    rand bit [6:0] d;
    bit [1:0] outer[4][2];
    bit [1:0] assoc[int];
    bit [1:0] over[65];
    constraint outerIndex {outer[c][0] == 1;}
    constraint assocIndex {assoc[int'(c)] == 1;}
    constraint overLimit {over[d] == 1;}
  endclass

  initial begin
    automatic NotCompared o = new;
    o.constraint_mode(0);
    `check_calls(o, 1'b1);
  end

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
