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

  task automatic incr(input int i, input int expected);
    arr[i] = x++;
    if (i < 5) `checkh(arr[i], expected);
  endtask

  function int get_y;
    y++;
    return y;
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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
