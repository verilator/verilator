// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  // String-key associative array with size constraint
  class StringKeyTest;
    rand int data[string];
    constraint c_size {data.size() == 3;}
  endclass

  // Int-key associative array with size constraint
  class IntKeyTest;
    rand bit [7:0] values[int];
    constraint c_size {values.size() == 2;}
  endclass

  initial begin
    automatic StringKeyTest str_obj = new();
    automatic IntKeyTest int_obj = new();
    automatic int rand_ok;

    // String-key: pre-populate 3 entries to match constraint
    str_obj.data["x"] = 0;
    str_obj.data["y"] = 0;
    str_obj.data["z"] = 0;

    rand_ok = str_obj.randomize();
    `checkd(rand_ok, 1);
    `checkd(str_obj.data.size(), 3);

    // Int-key: pre-populate 2 entries to match constraint
    int_obj.values[10] = 0;
    int_obj.values[20] = 0;

    rand_ok = int_obj.randomize();
    `checkd(rand_ok, 1);
    `checkd(int_obj.values.size(), 2);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
