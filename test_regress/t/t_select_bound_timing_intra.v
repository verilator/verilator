// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int arr[5];

  task automatic intra(input int i);
    time t = $time;
    arr[i] = #1 i;
    #1;
    if (i < 5) `checkh(arr[i], i);
    `checkh($time, t + 2);
  endtask

  initial begin
    intra(0);
    intra(7);
    intra(4);
    intra(1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
