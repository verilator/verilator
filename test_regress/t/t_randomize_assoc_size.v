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

  class AssocSizeTest;
    rand int data[string];
    constraint c_size { data.size() == 3; }
  endclass

  initial begin
    automatic AssocSizeTest obj = new();
    automatic int rand_ok;

    // Pre-populate with 3 entries to match the size constraint
    obj.data["x"] = 0;
    obj.data["y"] = 0;
    obj.data["z"] = 0;

    rand_ok = obj.randomize();
    `checkd(rand_ok, 1);
    `checkd(obj.data.size(), 3);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
