// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// Comprehensive test that item.index in array reduction constraints is supported

// Test 1: Basic item.index with sum
class Test1_BasicSum;
  rand int data[5];

  constraint c {
     // Use item.index in sum - indices 0,1,2,3,4 sum to 10
     data.sum() with (item.index) <= 10;
  }
endclass

// Test 2: item.index with arithmetic
class Test2_IndexTimesTwo;
  rand int data[5];

  constraint c {
     // Index * 2: 0,2,4,6,8 sum to 20
     data.sum() with (item.index * 2) == 20;
  }
endclass

// Test 3: item + item.index
class Test3_ItemPlusIndex;
  rand int data[3];

  constraint c {
     // item + index for each element
     data.sum() with (item + item.index) <= 50;
  }
endclass

// Test 4: item.index with product
class Test4_Product;
  rand int data[4];

  constraint c {
     // Product with index+1 to avoid zeros
     data.product() with (item.index + 1) <= 24;  // 1*2*3*4 = 24
  }
endclass

// Test 5: item.index with conditional
class Test5_Conditional;
  rand int data[6];

  constraint c {
     // Only sum indices that are even
     data.sum() with ((item.index % 2 == 0) ? item.index : 0) <= 6;  // 0+2+4 = 6
  }
endclass

// Test 6: item.index with XOR
class Test6_Xor;
  rand int data[4];

  constraint c {
     data.xor() with (item.index) >= 0;
  }
endclass

// Test 7: item.index with AND
class Test7_And;
  rand int data[4];

  constraint c {
     data.and() with (item + item.index) != 0;
  }
endclass

// Test 8: item.index with OR
class Test8_Or;
  rand int data[4];

  constraint c {
     data.or() with (item - item.index) >= -10;
  }
endclass

// Test 9: Complex expression with item.index
class Test9_Complex;
  rand int data[4];

  constraint c {
     // Multiple uses of item.index
     data.sum() with ((item.index * item.index) + item) <= 100;
  }
endclass

// Test 10: Dynamic array
class Test10_Dynamic;
  rand int data[];

  function new();
    data = new[4];
  endfunction

  constraint c_size {
    data.size() == 4;
  }

  constraint c {
     data.sum() with (item.index) <= 6;  // 0+1+2+3 = 6
  }
endclass

// Test 11: Larger array
class Test11_LargerArray;
  rand int data[10];

  constraint c {
     data.sum() with (item.index) == 45;  // 0+1+2+...+9 = 45
  }
endclass

// Test 12: item.index with negative values
class Test12_Negative;
  rand int data[5];

  constraint c {
     data.sum() with (item.index - 2) <= 5;  // -2,-1,0,1,2 = 0
  }
endclass

// Test 13: Just item (no index) - baseline test
class Test13_JustItem;
  rand int data[3];

  constraint c {
     data.sum() with (item) <= 30;
  }
endclass

// Test 14: item.index only (no item reference)
class Test14_IndexOnly;
  rand int data[5];

  constraint c {
     data.sum() with (item.index + 10) <= 60;  // 10,11,12,13,14 = 60
  }
endclass

// Test 15: Position-dependent weighting
class Test15_PositionWeight;
  rand int data[6];

  constraint c {
     // Later elements weighted more heavily: item * index
     data.sum() with (item * item.index) <= 200;
     foreach (data[i]) data[i] inside {[1:10]};
  }
endclass

// Test 16: Alternating pattern based on index
class Test16_AlternatingPattern;
  rand int data[8];

  constraint c {
     // Alternating positive/negative based on even/odd index
     data.sum() with ((item.index % 2 != 0) ? item : -item) >= -20;
     data.sum() with ((item.index % 2 != 0) ? item : -item) <= 20;
     foreach (data[i]) data[i] inside {[1:10]};
  }
endclass

// Test 17: Index-based bounds
class Test17_IndexBounds;
  rand int data[5];

  constraint c {
     // Each element should be within [0, index*2]
     data.sum() with ((item >= 0 && item <= item.index*2) ? item : 0) <= 40;
     foreach (data[i]) data[i] inside {[0:i*2]};
  }
endclass

// Test 18: Progressive constraint
class Test18_Progressive;
  rand int data[6];

  constraint c {
     // Count how many elements are greater than their index
     data.sum() with ((item > item.index) ? 1 : 0) >= 3;
     foreach (data[i]) data[i] inside {[0:10]};
  }
endclass

// Test 19: Distance from middle
class Test19_DistanceFromMiddle;
  rand int data[10];

  constraint c {
     // Weight by distance from middle index
     data.sum() with (item * ((item.index < 5) ? item.index : (9 - item.index))) <= 500;
     foreach (data[i]) data[i] inside {[1:10]};
  }
endclass

// Test 20: First half vs second half
class Test20_HalfConstraint;
  rand int data[8];

  constraint c {
     // First half sum should be less than second half sum
     data.sum() with ((item.index < 4) ? item : 0) <=
     data.sum() with ((item.index >= 4) ? item : 0);
     foreach (data[i]) data[i] inside {[1:20]};
  }
endclass

// Test 21: Modulo patterns
class Test21_ModuloPattern;
  rand int data[12];

  constraint c {
     // Sum every third element (indices 0,3,6,9)
     data.sum() with (((item.index % 3) == 0) ? item : 0) <= 40;
     foreach (data[i]) data[i] inside {[1:15]};
  }
endclass

// Test 22: Index power
class Test22_IndexPower;
  rand int data[5];

  constraint c {
     // Use index squared as multiplier
     data.sum() with (item * (item.index * item.index)) <= 1000;
     foreach (data[i]) data[i] inside {[1:10]};
  }
endclass

// Test 23: Boundary elements
class Test23_BoundaryElements;
  rand int data[10];

  constraint c {
     // First and last elements should dominate
     data.sum() with ((item.index == 0 || item.index == 9) ? item*3 : item) <= 150;
     foreach (data[i]) data[i] inside {[1:20]};
  }
endclass

// Test 24: Cascading constraint
class Test24_CascadingConstraint;
  rand int data[7];

  constraint c {
     // Each position contributes: item * (index + 1)
     data.sum() with (item * (item.index + 1)) <= 300;
     foreach (data[i]) data[i] inside {[1:10]};
  }
endclass

module t;
  initial begin
     Test1_BasicSum t1;
     Test2_IndexTimesTwo t2;
     Test3_ItemPlusIndex t3;
     Test4_Product t4;
     Test5_Conditional t5;
     Test6_Xor t6;
     Test7_And t7;
     Test8_Or t8;
     Test9_Complex t9;
     Test10_Dynamic t10;
     Test11_LargerArray t11;
     Test12_Negative t12;
     Test13_JustItem t13;
     Test14_IndexOnly t14;
     Test15_PositionWeight t15;
     Test16_AlternatingPattern t16;
     Test17_IndexBounds t17;
     Test18_Progressive t18;
     Test19_DistanceFromMiddle t19;
     Test20_HalfConstraint t20;
     Test21_ModuloPattern t21;
     Test22_IndexPower t22;
     Test23_BoundaryElements t23;
     Test24_CascadingConstraint t24;
     int i;

     // Test 1: Basic sum
     t1 = new;
     i = t1.randomize();
     `checkd(i, 1)

     // Test 2: Index times two
     t2 = new;
     i = t2.randomize();
     `checkd(i, 1)

     // Test 3: Item plus index
     t3 = new;
     i = t3.randomize();
     `checkd(i, 1)

     // Test 4: Product
     t4 = new;
     i = t4.randomize();
     `checkd(i, 1)

     // Test 5: Conditional
     t5 = new;
     i = t5.randomize();
     `checkd(i, 1)

     // Test 6: XOR
     t6 = new;
     i = t6.randomize();
     `checkd(i, 1)

     // Test 7: AND
     t7 = new;
     i = t7.randomize();
     `checkd(i, 1)

     // Test 8: OR
     t8 = new;
     i = t8.randomize();
     `checkd(i, 1)

     // Test 9: Complex
     t9 = new;
     i = t9.randomize();
     `checkd(i, 1)

     // Test 10: Dynamic array
     t10 = new;
     i = t10.randomize();
     `checkd(i, 1)

     // Test 11: Larger array
     t11 = new;
     i = t11.randomize();
     `checkd(i, 1)

     // Test 12: Negative
     t12 = new;
     i = t12.randomize();
     `checkd(i, 1)

     // Test 13: Just item
     t13 = new;
     i = t13.randomize();
     `checkd(i, 1)

     // Test 14: Index only
     t14 = new;
     i = t14.randomize();
     `checkd(i, 1)

     // Test 15: Position weight
     t15 = new;
     i = t15.randomize();
     `checkd(i, 1)

     // Test 16: Alternating pattern
     t16 = new;
     i = t16.randomize();
     `checkd(i, 1)

     // Test 17: Index bounds
     t17 = new;
     i = t17.randomize();
     `checkd(i, 1)

     // Test 18: Progressive
     t18 = new;
     i = t18.randomize();
     `checkd(i, 1)

     // Test 19: Distance from middle
     t19 = new;
     i = t19.randomize();
     `checkd(i, 1)

     // Test 20: Half constraint
     t20 = new;
     i = t20.randomize();
     `checkd(i, 1)

     // Test 21: Modulo pattern
     t21 = new;
     i = t21.randomize();
     `checkd(i, 1)

     // Test 22: Index power
     t22 = new;
     i = t22.randomize();
     `checkd(i, 1)

     // Test 23: Boundary elements
     t23 = new;
     i = t23.randomize();
     `checkd(i, 1)

     // Test 24: Cascading constraint
     t24 = new;
     i = t24.randomize();
     `checkd(i, 1)

     $write("*-* All Finished *-*\n");
     $finish;
  end
endmodule
