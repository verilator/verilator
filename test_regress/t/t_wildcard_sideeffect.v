// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  initial begin
    int a;
    int dict1d[*];
    int dict2d[*][*];
    int dict3d[*][*][*];
    int dictmix[int] [*];

    `checkd(dict1d[0], 0);
    `checkd(dict1d.size(), 0);
    `checkd(dict2d[0][0], 0);
    `checkd(dict2d.size(), 0);
    `checkd(dict3d[0][0][0], 0);
    `checkd(dict3d.size(), 0);
    `checkd(dictmix[0][0], 0);
    `checkd(dictmix.size(), 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
