// DESCRIPTION: Verilator: Test for unbounded '$' in inside range
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    int value;

    // Test [$:100] - should match minimum to 100
    value = 50;
    if (!(value inside {[$ : 100]})) $stop;

    value = 100;
    if (!(value inside {[$ : 100]})) $stop;

    value = 101;
    if (value inside {[$ : 100]}) $stop;  // Should NOT match

    // Test [0:$] - should match 0 to maximum
    value = 50;
    if (!(value inside {[0 : $]})) $stop;

    value = 0;
    if (!(value inside {[0 : $]})) $stop;

    // Test [100:$] - should match 100 to maximum
    value = 100;
    if (!(value inside {[100 : $]})) $stop;

    value = 200;
    if (!(value inside {[100 : $]})) $stop;

    value = 50;
    if (value inside {[100 : $]}) $stop;  // Should NOT match

    // Test mixed with other ranges
    value = 5;
    if (!(value inside {[$ : 10], [90 : $]})) $stop;

    value = 95;
    if (!(value inside {[$ : 10], [90 : $]})) $stop;

    value = 50;
    if (value inside {[$ : 10], [90 : $]}) $stop;  // Should NOT match

    // Test with function
    if (!(get_value(50) inside {[$ : 100]})) $stop;
    if (!(get_value(50) inside {[0 : $]})) $stop;
    if (get_value(50) inside {[100 : $]}) $stop;  // Should NOT match

    // Test with increment
    value = 49;
    if (!(++value inside {[$ : 100]})) $stop;  // value becomes 50
    if (value != 50) $stop;

    value = -1;
    if (!(++value inside {[0 : $]})) $stop;  // value becomes 0
    if (value != 0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

  function int get_value(int v);
    return v;
  endfunction

  // Use volatile-like behavior to prevent compile-time optimization
  int runtime_val;
  function int get_runtime_value(int v);
`ifdef VERILATOR
    runtime_val = $c32(v);
`else
    runtime_val = v;
`endif
    return runtime_val;
  endfunction
endmodule
