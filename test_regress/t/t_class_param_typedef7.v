// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test for issue #5461: Class parameter type using cls#()::typedef

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Basic parameterized class with a typedef
class cls1 #(bit PARAM = 0);
  typedef bit bool_t;
  typedef logic [7:0] byte_t;
endclass

// Class whose parameter TYPE is a typedef from a parameterized class (default params)
class cls2 #(cls1#()::bool_t PARAM = 1);
  function int get_param();
    return int'(PARAM);
  endfunction
endclass

// Class using non-default params for the referenced class
class cls3 #(cls1#(1)::bool_t PARAM = 0);
  function int get_param();
    return int'(PARAM);
  endfunction
endclass

// Class using a wider typedef from the parameterized class
class cls4 #(cls1#()::byte_t PARAM = 8'hAB);
  function int get_param();
    return int'(PARAM);
  endfunction
endclass

module t;
  initial begin
    automatic cls2#(1) obj2 = new;
    automatic cls3#(1) obj3 = new;
    automatic cls4#(8'hCD) obj4 = new;
    // Default param
    automatic cls2 obj2d = new;

    `checkd(obj2.get_param(), 1);
    `checkd(obj3.get_param(), 1);
    `checkd(obj4.get_param(), 'hCD);
    `checkd(obj2d.get_param(), 1);

    `checkd($bits(cls1#()::bool_t), 1);
    `checkd($bits(cls1#(1)::bool_t), 1);
    `checkd($bits(cls1#()::byte_t), 8);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
