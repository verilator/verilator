// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test that item.index in array reduction constraints is supported
// Test: Basic item.index usage with sum
class Test1_BasicIndex;
  rand bit [3:0] data[5];

  constraint c {
    // Sum of indices: 0+1+2+3+4 = 10
    // Cast to match result type (32-bit)
    data.sum() with (item.index) <= 10;
  }
endclass

// Test: item.index with item in expression
class Test2_IndexPlusItem;
  rand bit [3:0] data[5];

  constraint c {
    // Cast both to same width for expression
    data.sum() with (int'(item) + item.index) <= 50;
  }
endclass

// Test: Conditional based on index
class Test3_ConditionalOnIndex;
  rand bit [3:0] data[5];

  constraint c {
    // Only sum items at even indices
    data.sum() with ((item.index % 2 == 0) ? int'(item) : 0) <= 20;
  }
endclass

// Test: item.index with product
class Test4_ProductWithIndex;
  rand bit [2:0] data[4];

  constraint c {
    // Product of (item + index + 1) to avoid zero
    data.product() with (int'(item) + item.index + 1) <= 1000;
  }
endclass

// Test: item.index with xor (using 32-bit result)
class Test5_XorWithIndex;
  rand int data[4];

  constraint c {
    // Use int array so no casting needed
    data.xor() with (item ^ item.index) >= 0;
  }
endclass

// Test: item.index with and (using 32-bit result)
class Test6_AndWithIndex;
  rand int data[4];

  constraint c {data.and() with (item | item.index) != 0;}
endclass

// Test: item.index with or (using 32-bit result)
class Test7_OrWithIndex;
  rand int data[4];

  constraint c {data.or() with (item & item.index) >= 0;}
endclass

// Test: Complex expression with multiple uses
class Test8_ComplexExpression;
  rand bit [3:0] data[6];

  constraint c {
    // Use item.index multiple times in expression
    data.sum() with (int'(item) * item.index + item.index) <= 100;
  }
endclass

// Test: Just item.index (no item reference)
class Test9_JustIndex;
  rand bit [3:0] data[5];

  constraint c {
    // This tests sum of just indices
    data.sum() with (item.index * 2) == 20;  // 0+2+4+6+8 = 20
  }
endclass

// Test: Dynamic array with item.index
class Test10_DynamicArray;
  rand bit [3:0] dyn_data[];

  function new();
    dyn_data = new[5];
  endfunction

  constraint c_size {dyn_data.size() == 5;}

  constraint c {
    // item.index with dynamic array
    dyn_data.sum() with (item.index) <= 10;
  }
endclass

// Test: Larger array (16 elements)
class Test11_LargerArray;
  rand bit [3:0] data[16];

  constraint c {
    // Sum of indices: 0+1+2+...+15 = 120
    data.sum() with (item.index) <= 120;
  }
endclass

// Test: Large array with complex expression
class Test12_LargeComplex;
  rand int data[20];

  constraint c {
    // Complex expression with larger array
    data.sum() with ((item.index < 10) ? item : item * 2) <= 5000;
    foreach (data[i]) data[i] inside {[1 : 100]};
  }
endclass

// Test: Very large array (stress test)
class Test13_VeryLargeArray;
  rand int data[50];

  constraint c {
    // Test scalability - sum of first 50 indices = 1225
    data.sum() with (item.index) == 1225;
  }
endclass

// Test: Foreach on empty array
class Test14_EmptyArray;
  rand int empty[];

  function new;
    empty = new[0];
  endfunction

  constraint c {
    foreach (empty[i]) {
      empty[i] == 0;
    }
  }
endclass

// Test: Foreach on empty and not empty array
class Test15_EmptyAndNotEmptyArray;
  rand int empty[];
  rand int notEmpty[];

  function new;
    empty = new[0];
    notEmpty = new[10];
  endfunction

  constraint c {
    foreach (empty[i]) {
      empty[i] == 0;
    }
    foreach (notEmpty[i]) {
      notEmpty[i] == 'hDEADBEEF;
    }
  }
endclass

module t;
  initial begin
    Test1_BasicIndex t1;
    Test2_IndexPlusItem t2;
    Test3_ConditionalOnIndex t3;
    Test4_ProductWithIndex t4;
    Test5_XorWithIndex t5;
    Test6_AndWithIndex t6;
    Test7_OrWithIndex t7;
    Test8_ComplexExpression t8;
    Test9_JustIndex t9;
    Test10_DynamicArray t10;
    Test11_LargerArray t11;
    Test12_LargeComplex t12;
    Test13_VeryLargeArray t13;
    Test14_EmptyArray t14;
    Test15_EmptyAndNotEmptyArray t15;
    int i;

    // Test: Basic index
    t1 = new;
    i = t1.randomize();
    `checkd(i, 1)

    // Test: Index plus item
    t2 = new;
    i = t2.randomize();
    `checkd(i, 1)

    // Test: Conditional on index
    t3 = new;
    i = t3.randomize();
    `checkd(i, 1)

    // Test: Product with index
    t4 = new;
    i = t4.randomize();
    `checkd(i, 1)

    // Test: XOR with index
    t5 = new;
    i = t5.randomize();
    `checkd(i, 1)

    // Test: AND with index
    t6 = new;
    i = t6.randomize();
    `checkd(i, 1)

    // Test: OR with index
    t7 = new;
    i = t7.randomize();
    `checkd(i, 1)

    // Test: Complex expression
    t8 = new;
    i = t8.randomize();
    `checkd(i, 1)

    // Test: Just index
    t9 = new;
    i = t9.randomize();
    `checkd(i, 1)

    // Test: Dynamic array
    t10 = new;
    i = t10.randomize();
    `checkd(i, 1)

    // Test: Larger array (16 elements)
    t11 = new;
    i = t11.randomize();
    `checkd(i, 1)

    // Test: Large complex
    t12 = new;
    i = t12.randomize();
    `checkd(i, 1)

    // Test: Very large array (50 elements)
    t13 = new;
    i = t13.randomize();
    `checkd(i, 1)

    // Test: Foreach on empty array
    t14 = new;
    i = t14.randomize();
    `checkd(i, 1)

    // Test: Foreach on empty and not empty array
    t15 = new;
    i = t15.randomize();
    `checkd(i, 1)
    foreach (t15.notEmpty[i]) begin
        `checkd(t15.notEmpty[i], 'hDEADBEEF);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
