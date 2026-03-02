// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

class FuncConstraintTest;
  rand bit [7:0] value;
  rand bit [7:0] mask;

  function bit [7:0] get_min_value(bit [7:0] m);
    return m & 8'hF0;
  endfunction

  function bit [7:0] get_max_value(bit [7:0] m);
    return m | 8'h0F;
  endfunction

  constraint func_con {
    mask inside {[8'h10 : 8'hF0]};
    value >= get_min_value(mask);
    value <= get_max_value(mask);
  }

  function new();
  endfunction
endclass

module t;
  FuncConstraintTest fct;
  int rand_ok;
  bit [7:0] min_val;
  bit [7:0] max_val;

  initial begin
    fct = new();

    repeat (10) begin
      rand_ok = fct.randomize();
      `checkd(rand_ok, 1)

      `check_range(fct.mask, 8'h10, 8'hF0)

      min_val = fct.get_min_value(fct.mask);
      max_val = fct.get_max_value(fct.mask);
      `check_range(fct.value, min_val, max_val)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
