// DESCRIPTION: Verilator: Static class properties in nested constraints
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class base;
  static int limit;

  static function int get_limit();
    return limit + 1;
  endfunction
endclass

class child extends base;
  rand int value;
  rand int function_value;
  constraint selected {value == base::limit;}
  constraint selected_function {function_value == base::get_limit();}
endclass

class group_t;
  rand child item = new;
  constraint nonnegative {item.value <= 100;}
endclass

module t;
  initial begin
    group_t g;
    int randomize_result;
    g = new;
    for (int i = 1; i < 3; i++) begin
      base::limit = i * 17;
      randomize_result = g.randomize();
      `checkd(randomize_result, 1);
      `checkd(g.item.value, base::limit);
      `checkd(g.item.function_value, base::limit + 1);
    end
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
