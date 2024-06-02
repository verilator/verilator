// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
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
      // enum types does not match with other types (IEEE 1800-2023 6.22.1 and 6.22.4)
      // The assignment and the function call should throw an error.
      Converter#(bit) conv2 = conv1;
      conv1.toInt(0);
      $stop;
   end
endmodule
