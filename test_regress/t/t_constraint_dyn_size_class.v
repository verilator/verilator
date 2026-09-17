// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%d exp=%d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv, minv, maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
`define check_rand(cl, field, cond) \
begin \
  automatic longint prev_result; \
  automatic int ok; \
  if (!bit'(cl.randomize())) $stop; \
  prev_result = longint'(field); \
  if (!(cond)) $stop; \
  repeat(10) begin \
    longint result; \
    if (!bit'(cl.randomize())) $stop; \
    result = longint'(field); \
    if (!(cond)) $stop; \
    if (result != prev_result) ok = 1; \
    prev_result = result; \
  end \
  if (ok != 1) $stop; \
end

`define check_rand_foreach(cl, arr, arr_minsize, arr_maxsize, cond) \
begin \
  automatic int size_count = arr_maxsize - arr_minsize + 1; \
  automatic int max_randomize_count = size_count*20; \
  automatic int loop_count = 0; \
  automatic int occurence_ok = 0; \
  automatic longint size_occurence_count[int]; \
  automatic longint prev_results[arr_maxsize]; \
  automatic int ok[arr_minsize]; \
  if (!bit'(cl.randomize())) $stop; \
  for (int i = 0; i < arr.size(); i++) begin \
    prev_results[i] = longint'(arr[i]); \
  end \
  foreach (arr[i]) begin \
    if (!(cond)) $stop; \
  end \
  while (loop_count < max_randomize_count) begin \
    occurence_ok = 0; \
    if (!bit'(cl.randomize())) $stop; \
    for (int i = 0; i < arr.size(); i++) begin \
      if (longint'(arr[i]) != prev_results[i]) ok[i] = 1; \
      prev_results[i] = longint'(arr[i]); \
    end \
    foreach (arr[i]) begin \
      if (!(cond)) $stop; \
    end \
    size_occurence_count[arr.size()]++; \
    foreach (size_occurence_count[i]) begin \
      if (size_occurence_count[i] >= 3) occurence_ok++; \
    end \
    if (occurence_ok == size_count) break; \
    loop_count++; \
  end \
  if (loop_count >= max_randomize_count) $stop; \
  foreach (ok[i]) begin \
    if (ok[i] != 1) $stop; \
  end \
end

// verilog_format: on
// verilator lint_on

class SubSubClass;
  rand int subVal;
  rand int subArr[];

  constraint c {subArr.size < 10;}
endclass

class SubClass;
  rand int subVal;
  rand int subArr[];
  rand int assocArr[string] = '{"test": 1, "test2" : 2};
  SubSubClass ssc;

  function new();
    ssc = new;
    ssc.randomize();
  endfunction
endclass

class IndepClass;
  rand int val0;
  rand int val1;
  rand int val2;
  rand SubClass sc;

  function new();
    sc = new;
  endfunction
endclass

class BaseClass;
  rand int arr[];
  // Size-constrained array
  constraint bc {
    arr.size < 10;
    arr.size > 5;
  }
  ;
endclass

class ExtClass0 extends BaseClass;
  function int randomize_gpr(IndepClass cls);
    return (cls.randomize() with {
      // If with arr.size on array, that's a field of class
      // calling randomize() with
      if (arr.size > 0) {val0 inside {arr};}

      // If with arr.size on array thats a field inside subclass
      // chain
      if (cls.sc.ssc.subArr.size > 0) {val1 == 'hDEADBEEF;}

      // Randomizable array size
      sc.subArr.size > 25;
      sc.subArr.size < 50;

      // If with associative array size
      if (sc.assocArr.size > 0) {val2 == 'hCAFEBABE;}
    });
  endfunction
endclass

class ExtClass1 extends BaseClass;
  // Class that extends BaseClass and uses arr.size variable
  constraint c {
    unique {arr};
    foreach (arr[i]) {arr[i] != 0;}
  }
endclass

typedef int arr_tdef[];

class InnerSizeElem;
  rand int arr[];
  rand arr_tdef tdef;

  constraint c {
    tdef.size <= 5;
    tdef.size >= 3;

    arr.size <= 5;
    arr.size >= 3;

    foreach (arr[i]) {
      arr[i] >= 'hAAAAAAAA;
      arr[i] <= 'hBBBBBBBB;
    }
  };
endclass

class InnerElem;
  rand arr_tdef tdef;
  rand int arr[];

  constraint c {
    foreach (arr[i]) {
      arr[i] >= 'hEEEEEEEE;
      arr[i] <= 'hFEEEEEEE;
    }
  };
endclass

class InnerSize;
  rand arr_tdef tdef;
  rand int arr[];

  constraint c {
    tdef.size <= 6;
    tdef.size >= 3;

    arr.size <= 6;
    arr.size >= 3;
  };
endclass

// Class with array-size constraint inside base class
class OuterEmpty extends InnerSizeElem;
endclass

// Class with array-size constraint inside base class and
// inside the class itself
class OuterElemAndSize extends InnerSizeElem;
  rand arr_tdef outer_tdef;
  rand int outer_arr[];

  constraint cc {
    outer_tdef.size <= 5;
    outer_tdef.size >= 3;

    outer_arr.size <= 5;
    outer_arr.size >= 3;

    foreach (outer_arr[i]) {
      outer_arr[i] >= 'hABBBBBBB;
      outer_arr[i] <= 'hBAAAAAAA;
    }
  };
endclass

class OuterElemInnerSize extends InnerSize;
  constraint cc {
    foreach(arr[i]) {
      arr[i] >= 'h44444444;
      arr[i] <= 'h55555555;
    }
  };
endclass

class OuterSizeInnerElem extends InnerElem;
  constraint cc {
    tdef.size <= 5;
    tdef.size >= 3;

    arr.size <= 5;
    arr.size >= 3;
  };
endclass

class OuterSizeInnerSize extends InnerSize;
  constraint cc {
    tdef.size <= 5;

    arr.size <= 5;
  };
endclass

module t;
  ExtClass0 ext0;
  ExtClass1 ext1;
  IndepClass indep;
  OuterEmpty outEmpt;
  OuterElemAndSize outElemSize;
  OuterElemInnerSize outElemInSize;
  OuterSizeInnerElem outSizeInElem;
  OuterSizeInnerSize outSizeInSize;

  initial begin
    int randomize_result;
    indep = new;
    ext0 = new;
    ext1 = new;
    outEmpt = new;
    outElemSize = new;
    outElemInSize = new;
    outSizeInElem = new;
    outSizeInSize = new;

    repeat (10) begin
      randomize_result = ext0.randomize();
      `checkd(randomize_result, 1);
      randomize_result = ext0.randomize();
      `checkd(randomize_result, 1);
      randomize_result = ext0.randomize_gpr(indep);
      `checkd(randomize_result, 1);

      `checkh(indep.val0 inside {ext0.arr}, 1);
      `checkh(indep.val1, 'hDEADBEEF);
      `checkh(indep.val2, 'hCAFEBABE);

      `check_range(ext0.arr.size(), 5, 10);
      `check_range(indep.sc.subArr.size(), 25, 50);

      foreach (ext0.arr[i]) begin
        if (ext0.arr[i] == 0) begin
          `stop;
        end
        foreach (ext0.arr[j]) begin
          if (i == j) continue;
          if (ext0.arr[i] == ext0.arr[j]) begin
            `stop;
          end
        end
      end
    end

    `check_rand(outEmpt, outEmpt.tdef.size(),
        (outEmpt.tdef.size() <= 5 && outEmpt.tdef.size() >= 3));
    `check_rand(outEmpt, outEmpt.arr.size(),
        (outEmpt.arr.size() <= 5 && outEmpt.arr.size() >= 3));
    `check_rand_foreach(outEmpt, outEmpt.arr, 3, 5,
        (outEmpt.arr[i] >= 'hAAAAAAAA && outEmpt.arr[i] <= 'hBBBBBBBB));

    `check_rand(outElemSize, outElemSize.outer_tdef.size(),
        (outElemSize.outer_tdef.size() <= 5 && outElemSize.outer_tdef.size() >= 3));
    `check_rand(outElemSize, outElemSize.arr.size(),
        (outElemSize.arr.size() <= 5 && outElemSize.arr.size() >= 3));
    `check_rand_foreach(outElemSize, outElemSize.arr, 3, 5,
        (outElemSize.arr[i] >= 'hAAAAAAAA && outElemSize.arr[i] <= 'hBBBBBBBB));
    `check_rand(outElemSize, outElemSize.outer_arr.size(),
        (outElemSize.outer_arr.size() <= 5 && outElemSize.outer_arr.size() >= 3));
    `check_rand_foreach(outElemSize, outElemSize.outer_arr, 3, 5,
        (outElemSize.outer_arr[i] >= 'hABBBBBBB && outElemSize.outer_arr[i] <= 'hBAAAAAAA));

    `check_rand(outElemInSize, outElemInSize.tdef.size(),
        (outElemInSize.tdef.size() <= 6 && outElemInSize.tdef.size() >= 3));
    `check_rand(outElemInSize, outElemInSize.arr.size(),
        (outElemInSize.arr.size() <= 6 && outElemInSize.arr.size() >= 3));
    `check_rand_foreach(outElemInSize, outElemInSize.arr, 3, 6,
        (outElemInSize.arr[i] >= 'h44444444 && outElemInSize.arr[i] <= 'h55555555));

    `check_rand(outSizeInElem, outSizeInElem.tdef.size(),
        (outSizeInElem.tdef.size() <= 5 && outSizeInElem.tdef.size() >= 3));
    `check_rand(outSizeInElem, outSizeInElem.arr.size(),
        (outSizeInElem.arr.size() <= 5 && outSizeInElem.arr.size() >= 3));
    `check_rand_foreach(outSizeInElem, outSizeInElem.arr, 3, 5,
        (outSizeInElem.arr[i] >= 'hEEEEEEEE && outSizeInElem.arr[i] <= 'hFEEEEEEE));

    `check_rand(outSizeInSize, outSizeInSize.tdef.size(),
        (outSizeInSize.tdef.size() >= 3 && outSizeInSize.tdef.size() <= 5));
    `check_rand(outSizeInSize, outSizeInSize.arr.size(),
        (outSizeInSize.arr.size() >= 3 && outSizeInSize.arr.size() <= 5));

    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule
