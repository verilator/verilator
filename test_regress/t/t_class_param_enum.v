// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

typedef enum bit {A = 0, B = 1} enum_t;

class Converter #(type T);
   function int toInt(T t);
      return int'(t);
   endfunction
endclass

module t;
   initial begin
      Converter#(enum_t) conv1 = new;
      Converter#(bit) conv2 = new;
      if (conv1.toInt(A) != 0) $stop;
      if (conv2.toInt(1) != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
