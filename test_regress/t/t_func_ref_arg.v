// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class MyInt;
  int x;
  function new(int a);
    x = a;
  endfunction
endclass

function int get_val_set_5(ref int x);
  automatic int y = x;
  x = 5;
  return y;
endfunction

class Cls;
  function int get_val_set_2(ref int x);
    automatic int y = x;
    x = 2;
    return y;
  endfunction
endclass

typedef struct {
  MyInt arr[2][][$];
} struct_t;

module t;
  int a, b;
  int arr[1];
  int dyn_arr[];
  int dyn_arr_2d[][];
  struct_t st;
  Cls cls;
  MyInt mi;
  initial begin
    a = 10;
    b = get_val_set_5(a);
    `checkh(a, 5);
    `checkh(b, 10);

    cls = new;
    b   = cls.get_val_set_2(a);
    `checkh(a, 2);
    `checkh(b, 5);

    mi = new(1);
    b  = cls.get_val_set_2(mi.x);
    `checkh(mi.x, 2);
    `checkh(b, 1);

    arr[0] = 10;
    b = cls.get_val_set_2(arr[0]);
    `checkh(arr[0], 2);
    `checkh(b, 10);

    dyn_arr = new[3];
    dyn_arr[1] = 10;
    b = get_val_set_5(dyn_arr[1]);
    `checkh(dyn_arr[1], 5);
    `checkh(b, 10);
    b = cls.get_val_set_2(dyn_arr[1]);
    `checkh(dyn_arr[1], 2);
    `checkh(b, 5);

    dyn_arr_2d = new[2];
    dyn_arr_2d[0] = new[4];
    dyn_arr_2d[0][1] = 10;
    b = get_val_set_5(dyn_arr_2d[0][1]);
    `checkh(dyn_arr_2d[0][1], 5);
    `checkh(b, 10);
    b = cls.get_val_set_2(dyn_arr_2d[0][1]);
    `checkh(dyn_arr_2d[0][1], 2);
    `checkh(b, 5);

    st.arr[1] = new[3];
    st.arr[1][2][0] = new(10);
    b = get_val_set_5(st.arr[1][2][0].x);
    `checkh(st.arr[1][2][0].x, 5);
    `checkh(b, 10);
    b = cls.get_val_set_2(st.arr[1][2][0].x);
    `checkh(st.arr[1][2][0].x, 2);
    `checkh(b, 5);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
