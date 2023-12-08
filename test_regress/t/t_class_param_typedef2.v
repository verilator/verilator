// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

virtual class Virt;
endclass

class MyInt;
  int x;
endclass

class uvm_object_registry #(
    type T = Virt
);
  static function T create_object();
    T obj = new();
    obj.x = 1;
    return obj;
  endfunction
endclass

typedef uvm_object_registry#(MyInt) type_id;

module t;
  initial begin
    MyInt mi = type_id::create_object();
    if (mi.x != 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
