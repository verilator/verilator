// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHTRUNC */
class Inner;
  rand int m_x;
  rand int m_y;
endclass

class Middle;
  rand Inner m_obj;
  rand Inner m_arr[3];
endclass

class Outer;
  rand Middle m_mid;
  rand Middle m_mid_arr[2];

  function new();
    m_mid = new;
    m_mid.m_obj = new;
    foreach (m_mid.m_arr[i]) m_mid.m_arr[i] = new;
    foreach (m_mid_arr[i]) begin
      m_mid_arr[i] = new;
      m_mid_arr[i].m_obj = new;
      foreach (m_mid_arr[i].m_arr[j]) m_mid_arr[i].m_arr[j] = new;
    end
  endfunction

  // Case 1: Simple nested member access (should work)
  constraint c_simple {
    m_mid.m_obj.m_x == 100;
    m_mid.m_obj.m_y == 101;
  }

  // Case 2: Array indexing in the path (may not work)
  constraint c_array_index {
    m_mid.m_arr[0].m_x == 200;
    m_mid.m_arr[0].m_y == 201;
  }

  // Case 3: Nested array indexing
  constraint c_nested_array {
    m_mid_arr[0].m_obj.m_x == 300;
    m_mid_arr[0].m_obj.m_y == 301;
  }

  // Case 4: Multiple array indices
  constraint c_multi_array {
    m_mid_arr[1].m_arr[2].m_y == 400;
  }
endclass

module t_constraint_global_arr_unsup;
  initial begin
    Outer o = new;
    if (o.randomize()) begin
      $display("Case 1 - Simple: mid.obj.x = %0d (expected 100)", o.m_mid.m_obj.m_x);
      $display("Case 1 - Simple: mid.obj.y = %0d (expected 101)", o.m_mid.m_obj.m_y);
      $display("Case 2 - Array[0]: mid.arr[0].x = %0d (expected 200)", o.m_mid.m_arr[0].m_x);
      $display("Case 2 - Array[0]: mid.arr[0].y = %0d (expected 201)", o.m_mid.m_arr[0].m_y);
      $display("Case 3 - Nested[0]: mid_arr[0].obj.x = %0d (expected 300)", o.m_mid_arr[0].m_obj.m_x);
      $display("Case 3 - Nested[0]: mid_arr[0].obj.y = %0d (expected 301)", o.m_mid_arr[0].m_obj.m_y);
      $display("Case 4 - Multi[1][2]: mid_arr[1].arr[2].y = %0d (expected 400)", o.m_mid_arr[1].m_arr[2].m_y);

      // Check results
      if (o.m_mid.m_obj.m_x == 100 && o.m_mid.m_obj.m_y == 101 &&
          o.m_mid.m_arr[0].m_x == 200 && o.m_mid.m_arr[0].m_y == 201 &&
          o.m_mid_arr[0].m_obj.m_x == 300 && o.m_mid_arr[0].m_obj.m_y == 301 &&
          o.m_mid_arr[1].m_arr[2].m_y == 400) begin
        $display("*-* All Finished *-*");
        $finish;
      end
      else begin
        $display("*-* FAILED *-*");
        $stop;
      end
    end
    else begin
      $display("*-* FAILED: randomize() returned 0 *-*");
      $stop;
    end
  end
endmodule
/* verilator lint_off WIDTHTRUNC */
