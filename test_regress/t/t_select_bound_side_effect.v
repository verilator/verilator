// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int arr[5];
  int x = 0;
  int y = 0;
  int z = 0;
  int w = 0;
  int q[$];

  task automatic incr(input int i, input int expected);
    arr[i] = x++;
    if (i < 5) `checkh(arr[i], expected);
  endtask

  function int get_y;
    y++;
    return y;
  endfunction

  function int get_w(int i);
    w++;
    return i;
  endfunction

  task automatic assign_side_effect(input int i, input int expected);
    arr[i] = get_y();
    if (i < 5) `checkh(arr[i], expected);
  endtask

  task automatic add_z(inout int a);
    a += z;
    z++;
  endtask

  task automatic assign_side_effect_inout(input int i, input int expected);
    if (i < 5) arr[i] = 1;
    add_z(arr[i]);
    if (i < 5) `checkh(arr[i], expected);
  endtask

  initial begin
    incr(0, 0);
    incr(7, 0);
    incr(4, 2);

    assign_side_effect(3, 1);
    assign_side_effect(8, 0);
    assign_side_effect(9, 0);
    assign_side_effect(3, 4);

    assign_side_effect_inout(3, 1);
    assign_side_effect_inout(4, 2);
    assign_side_effect_inout(5, 0);
    assign_side_effect_inout(1, 4);

    y = 0;
    for (int i = 0; i < 10; i++) begin
      arr[get_y()] = i;
      if (y < 5) `checkh(arr[y], i);
      `checkh(y, 2 * i + 1);
      arr[get_y()%(i+1)] = i;
      if (y % (i + 1) < 5) `checkh(arr[y%(i+1)], i);
      `checkh(y, 2 * (i + 1));
    end

    // Side effects in a 'with' clause of an index
    q = '{1, 2};
    arr[q.sum() with (get_w(item))] = 6;
    `checkh(arr[3], 6);
    `checkh(w, 2);
    // Index 7 is out of bounds of arr[5]: the write is dropped, but the index is evaluated once
    arr[q.sum() with (get_w(item))+4] = 7;
    `checkh(w, 4);
    `checkh(arr[3], 6);
    // Side effects in a 'with' clause are kept when its result is folded or unused
    begin
      int zero;
      zero = 0;
      y = (q.sum() with (get_w(item))) * zero;
      `checkh(w, 6);
      y = q.sum() with (get_w(item));
      y = 5;
      `checkh(w, 8);
    end
    // An index with a new value each evaluation is evaluated once
    for (int i = 0; i < 5; i++) arr[i] = 10 * i + 1;
    for (int seed = 1; seed <= 20; seed++) begin
      int got;
      int after;
      int pos;
      void'($urandom(seed));
      got = arr[$urandom() % 8];
      after = $urandom();
      void'($urandom(seed));
      pos = $urandom() % 8;
      `checkh(got, pos < 5 ? arr[pos] : 0);
      pos = $urandom();
      `checkh(after, pos);
    end
    // Likewise the index of an increment, and a value split into parts or tested against a set
    for (int seed = 1; seed <= 20; seed++) begin
      int after;
      int pos;
      logic [7:0] a8;
      logic [7:0] b8;
      bit in_set;
      for (int i = 0; i < 5; i++) arr[i] = 10 * i;
      void'($urandom(seed));
      arr[$urandom() % 5] += 1;
      {a8, b8} = 16'($urandom());
      in_set = ($urandom() % 8) inside {1, 3, 5};
      after = $urandom();
      void'($urandom(seed));
      pos = $urandom() % 5;
      `checkh(arr[pos], 10 * pos + 1);
      `checkh(arr.sum(), 101);
      pos = $urandom();
      `checkh({a8, b8}, 16'(pos));
      pos = $urandom() % 8;
      `checkh(in_set, pos == 1 || pos == 3 || pos == 5);
      pos = $urandom();
      `checkh(after, pos);
    end
    // An overwritten value is evaluated
    for (int seed = 1; seed <= 20; seed++) begin
      int unsigned r1;
      int unsigned r2;
      int unsigned r3;
      int unsigned x;
      int unsigned got;
      void'($urandom(seed));
      r1 = $urandom();
      r2 = $urandom();
      r3 = $urandom();
      void'($urandom(seed));
      x = $urandom();
      x = $urandom();
      got = $urandom();
      `checkh(x, r2);
      `checkh(got, r3);
    end
    // A replicated value is evaluated once (IEEE 1800-2023 11.4.12.1)
    for (int seed = 1; seed <= 20; seed++) begin
      logic [63:0] r64;
      logic [95:0] r96;
      int after;
      int pos;
      void'($urandom(seed));
      r64 = {2{$urandom()}};
      r96 = {3{$urandom()}};
      after = $urandom();
      void'($urandom(seed));
      pos = $urandom();
      `checkh(r64, {2{pos}});
      pos = $urandom();
      `checkh(r96, {3{pos}});
      pos = $urandom();
      `checkh(after, pos);
    end
    begin
      logic [63:0] r64;
      y = 0;
      r64 = {2{get_y()}};
      `checkh(y, 1);
      `checkh(r64, {2{32'd1}});
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
