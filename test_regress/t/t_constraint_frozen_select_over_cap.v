// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A randomized index into a table larger than the frozen-select expansion
// limit still solves while the table's mode is on, even though rand_mode()
// is called on it.
class over_cap_table;
  rand bit [7:0] frame;
  rand bit [7:0] target[20000][2];
  rand int idx;
  constraint c { idx == 12345; frame == target[idx][1]; target[12345][1] == 8'h5a; }
endclass

module t;
  initial begin
    automatic over_cap_table obj = new;
    automatic int ok;
    obj.target.rand_mode(0);
    obj.target.rand_mode(1);
    ok = obj.randomize();
    `checkd(ok, 1);
    `checkd(obj.idx, 12345);
    `checkd(obj.frame, 8'h5a);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
