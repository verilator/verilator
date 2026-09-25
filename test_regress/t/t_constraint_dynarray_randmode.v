// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {
  rand int value;
} entry_t;

class Container;
  rand entry_t items[];

  constraint c_value { items[0].value == 0; }
endclass

module t;
  initial begin
    automatic Container obj = new;
    automatic int randomize_result;
    repeat(20) begin
      obj.items = new[1];
      obj.items[0].value = 0;
      obj.items.rand_mode(0);
      randomize_result = obj.randomize();
      `checkd(randomize_result, 1)
      `checkd(obj.items.size(), 1)
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
