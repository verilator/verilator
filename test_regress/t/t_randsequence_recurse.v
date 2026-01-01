// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  initial begin

    int o;
    int i;
    o = 0;
    i = 0;

    randsequence(main)
      main : add /*1*/ add /*1*/ recurse /* 2 */ recurse /* 0 */;
      recurse: { i++; if (i >= 3) break; } add recurse;
      add: { o++; } ;
    endsequence

    `checkd(o, 4);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
