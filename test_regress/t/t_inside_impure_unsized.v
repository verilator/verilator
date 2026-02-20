// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;
  bit [7:0] str_arr[string];
  string str_key;

  bit [7:0] int_arr[int];
  int int_key;

  int counter = 0;
  function bit [7:0] get_val();
    counter++;
    return 25;
  endfunction

  initial begin
    str_arr["test"] = 25;
    str_key = "test";
    if (!(str_arr[str_key] inside {[10 : 50]})) $stop;
    if (str_arr[str_key] inside {[100 : 200]}) $stop;

    int_arr[0] = 25;
    int_key = 0;
    if (!(int_arr[int_key] inside {[10 : 50]})) $stop;
    if (int_arr[int_key] inside {[100 : 200]}) $stop;

    if (!(get_val() inside {[10 : 50]})) $stop;
    if (get_val() inside {[100 : 200]}) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
