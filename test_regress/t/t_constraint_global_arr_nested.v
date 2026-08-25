// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_rand(cl, field, cond) \
begin \
   automatic longint prev_result; \
   automatic int ok; \
   if (!bit'(cl.randomize())) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(9) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

/* verilator lint_off WIDTHTRUNC */
class Inner;
  rand int m_x;
  rand int m_y;
endclass

class Middle;
  rand Inner m_obj;
  rand Inner m_arr[3];
endclass

class Item;
  rand int x;
  rand int y;
  randc bit [1:0] cycle;
endclass

class Holder;
  rand Item cyclic[1];
  rand Item mode[1];
  rand Item items[2];
  rand Inner m_string_assoc[string];
  function new;
    mode[0] = new;
    cyclic[0] = new;
    m_string_assoc["abc"] = new;
    foreach (items[i])
      items[i] = new;
  endfunction
endclass

class Outer;
  int m_idx;
  rand Middle m_mid;
  rand Middle m_mid2;
  rand Middle m_mid_arr[3];
  rand Middle m_mid_arr2[3][2];
  rand Middle m_mid_arr3[3][2];
  rand Middle m_mid_arr4[3][2];
  rand Inner m_assoc[int];
  string m_key;
  rand Inner m_assoc_nested[int][bit];
  rand Holder m_holder;

  function new();
    m_idx = 1;
    m_key = "abc";
    m_mid = new;
    m_mid.m_obj = new;
    foreach (m_mid.m_arr[i]) m_mid.m_arr[i] = new;
    m_mid2 = new;
    foreach (m_mid2.m_arr[i]) m_mid2.m_arr[i] = new;
    foreach (m_mid_arr[i]) begin
      m_mid_arr[i] = new;
      m_mid_arr[i].m_obj = new;
      foreach (m_mid_arr[i].m_arr[j]) m_mid_arr[i].m_arr[j] = new;
    end
    foreach (m_mid_arr2[i])
      foreach (m_mid_arr2[i][j]) begin
        m_mid_arr2[i][j] = new;
        m_mid_arr2[i][j].m_obj = new;
        foreach (m_mid_arr2[i][j].m_arr[k]) m_mid_arr2[i][j].m_arr[k] = new;
      end
    foreach (m_mid_arr3[i])
      foreach (m_mid_arr3[i][j]) begin
        m_mid_arr3[i][j] = new;
        m_mid_arr3[i][j].m_obj = new;
        foreach (m_mid_arr3[i][j].m_arr[k]) m_mid_arr3[i][j].m_arr[k] = new;
      end
    foreach (m_mid_arr4[i])
      foreach (m_mid_arr4[i][j]) begin
        m_mid_arr4[i][j] = new;
        m_mid_arr4[i][j].m_obj = new;
        foreach (m_mid_arr4[i][j].m_arr[k]) m_mid_arr4[i][j].m_arr[k] = new;
      end

    m_assoc[0] = new;
    m_assoc[1] = new;
    m_assoc_nested[123][1] = new;
    m_holder = new;
  endfunction

  // Case 1: Simple nested member access
  constraint c_simple {
    m_mid.m_obj.m_x == 100;
    m_mid.m_obj.m_y == 101;
  }

  // Case 2: Array indexing in the path
  constraint c_array_index {
    m_mid.m_arr[0].m_x == 200;
    m_mid.m_arr[0].m_y == 201;

    m_mid2.m_arr[0].m_x < 200;
    m_mid2.m_arr[0].m_y < 201;
  }

  constraint c_array_index_idx {
    m_mid.m_arr[m_idx].m_x == 202;
    m_mid.m_arr[m_idx].m_y == 203;

    m_mid2.m_arr[m_idx].m_x < 202;
    m_mid2.m_arr[m_idx].m_y < 203;
  }

  // Case 3: Nested array indexing
  constraint c_nested_array {
    m_mid_arr[0].m_obj.m_x == 300;
    m_mid_arr[0].m_obj.m_y == 301;
  }

  // Case 4: Multiple array indices
  constraint c_multi_array {
    m_mid_arr[1].m_arr[2].m_y == 400;

    m_mid_arr[2].m_arr[2].m_y < 400;
  }

  // Case 5: Associative array element member access
  constraint c_assoc {
    m_assoc[0].m_x == 500;
    m_assoc[m_idx].m_x == 502;
  }

  constraint c_string_assoc {
    m_holder.m_string_assoc[m_key].m_x == 43;
    m_holder.m_string_assoc[m_key].m_y < 43;
  }

  constraint c_assoc_nested {
    m_assoc_nested[123][1].m_x == 501;
  }

  // Case 6: foreach
  constraint c_foreach {
    foreach (m_mid_arr2[i, j])
      m_mid_arr2[i][j].m_obj.m_x == i + j;
  }
  constraint c_foreach2 {
    foreach (m_mid_arr3[i])
      foreach (m_mid_arr3[i][j])
        m_mid_arr3[i][j].m_obj.m_x == i - j;
  }

  constraint c_foreach3 {
    foreach (m_mid_arr4[i])
        m_mid_arr4[i][m_idx].m_obj.m_x == i;
  }

  constraint c_foreach_multiple {
    foreach(m_holder.items[i]) {
      m_holder.items[i].x == i;
      m_holder.items[i].y == i + 10;
    }
  }

  // Case 7: randmode
  constraint c_mode {
    m_holder.mode[0].x == 42;
  }

  // Case 8: randc
  constraint c_randc {
    m_holder.cyclic[0].cycle inside {[0:3]};
  }
endclass


module t_constraint_global_arr_nested;
  initial begin
    automatic Outer o = new;
    automatic Outer randc_o = new;
    automatic Outer randmode_off_o = new;
    automatic bit [3:0] seen = 0;

    if (randmode_off_o.randomize() != 1) $stop;
    `checkd(randmode_off_o.m_holder.mode[0].x, 42);

    o.m_holder.mode[0].x = 42;
    o.m_holder.mode[0].x.rand_mode(0);

    if (o.randomize() != 1) $stop;

    foreach (o.m_mid_arr2[i])
      foreach (o.m_mid_arr2[i][j])
        if (o.m_mid_arr2[i][j].m_obj.m_x != i + j) $stop;
    foreach (o.m_mid_arr3[i])
      foreach (o.m_mid_arr3[i][j])
        if (o.m_mid_arr3[i][j].m_obj.m_x != i - j) $stop;
    foreach (o.m_mid_arr4[i])
      if (o.m_mid_arr4[i][1].m_obj.m_x != i) $stop;
    `checkd(o.m_mid.m_obj.m_x, 100);
    `checkd(o.m_mid.m_obj.m_y, 101);
    `checkd(o.m_mid.m_arr[0].m_x, 200);
    `checkd(o.m_mid.m_arr[0].m_y, 201);
    `checkd(o.m_mid.m_arr[1].m_x, 202);
    `checkd(o.m_mid.m_arr[1].m_y, 203);
    `checkd(o.m_mid_arr[0].m_obj.m_x, 300);
    `checkd(o.m_mid_arr[0].m_obj.m_y, 301);
    `checkd(o.m_mid_arr[1].m_arr[2].m_y, 400);
    `checkd(o.m_assoc[0].m_x, 500);
    `checkd(o.m_assoc[1].m_x, 502);
    `checkd(o.m_holder.m_string_assoc["abc"].m_x, 43);
    `checkd(o.m_assoc_nested[123][1].m_x, 501);
    `checkd(o.m_holder.mode[0].x, 42);
    foreach (o.m_holder.items[i]) begin
      `checkd(o.m_holder.items[i].x, i);
      `checkd(o.m_holder.items[i].y, i + 10);
    end
    `check_rand(o, o.m_mid2.m_arr[0].m_x, o.m_mid2.m_arr[0].m_x < 200);
    `check_rand(o, o.m_mid2.m_arr[0].m_y, o.m_mid2.m_arr[0].m_y < 201);

    `check_rand(o, o.m_mid2.m_arr[1].m_x, o.m_mid2.m_arr[1].m_x < 202);
    `check_rand(o, o.m_mid2.m_arr[1].m_y, o.m_mid2.m_arr[1].m_y < 203);

    `check_rand(o, o.m_mid_arr[2].m_arr[2].m_y, o.m_mid_arr[2].m_arr[2].m_y < 400);

    `check_rand(o, o.m_holder.m_string_assoc["abc"].m_y, o.m_holder.m_string_assoc["abc"].m_y < 43);

    repeat (4) begin
     if (randc_o.randomize() != 1)
       $fatal(1, "randc randomize failed");
     if (seen[randc_o.m_holder.cyclic[0].cycle])
       $fatal(1, "randc repeated early: %0d",
              randc_o.m_holder.cyclic[0].cycle);
     seen[randc_o.m_holder.cyclic[0].cycle] = 1;
    end
    if (seen != 4'b1111)
      $fatal(1, "randc did not complete the cycle");

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
