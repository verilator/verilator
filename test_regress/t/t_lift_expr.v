// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  function automatic int one();
    return 1;
  endfunction

  function automatic int two();
    /* verilator no_inline_task */
    return 2;
  endfunction

  class C;
    static int i = one() + 1;
    static int j = two() + 1;
  endclass

  initial begin
    `checkh(C::i, 2);
    `checkh(C::j, 3);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
