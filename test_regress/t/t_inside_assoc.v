// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  initial begin
    int aa[string];
    aa = '{default: 5};
    `checkd((5 inside {aa}), 0);
    aa["a"] = 7;
    `checkd((7 inside {aa}), 1);
    `checkd((3 inside {aa, 3}), 1);
    aa.delete("a");
    `checkd((7 inside {aa}), 0);
  end

  initial begin
    int wild[*];
    wild[9] = 8;
    `checkd((8 inside {wild}), 1);
    `checkd((9 inside {wild}), 0);
  end

  initial begin
    bit [95:0] wide[int];
    wide[1] = {32'h1, 64'h0};
    `checkd(({32'h1, 64'h0} inside {wide}), 1);
    `checkd(({32'h2, 64'h0} inside {wide}), 0);
  end

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
