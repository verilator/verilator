// DESCRIPTION: Verilator: Test for unbounded '$' in inside range
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wei-Lun Chiu
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

    // Test with side effects, evaluated even if the result is known
    cnt = 0;
    if (!(cnt_value(50) inside {[0 : $]})) $stop;
    if (cnt != 1) $stop;
    cnt = 0;
    if (!(cnt_byte() inside {[8'h00 : 8'hff]})) $stop;
    if (cnt != 1) $stop;

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

  int cnt;
  function int cnt_value(int v);
    ++cnt;
    return v;
  endfunction
  function logic [7:0] cnt_byte();
    ++cnt;
    return 8'd3;
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
