// DESCRIPTION: Verilator: Localparam with package function call using computed interface param
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package pkg;
  function automatic bit fn(int value);
    return (value > 0) ? 1'b1 : 1'b0;
  endfunction
endpackage

interface ifc #(parameter int WIDTH = 8);
  localparam int DEPTH = $clog2(WIDTH);
  localparam int COMPUTED = DEPTH * 2;
endinterface

module mod(ifc i);
  // LPARAM references i.COMPUTED which depends on i.DEPTH which depends on WIDTH
  localparam bit lpbit = pkg::fn(i.COMPUTED);
  localparam int lpval = i.COMPUTED + 1;
endmodule

module t;
  ifc #(.WIDTH(64)) i();
  mod m(.i);

  initial begin
    // DEPTH = $clog2(64) = 6, COMPUTED = 6*2 = 12
    `checkd(m.lpbit, 1'b1);  // fn(12) returns 1 since 12 > 0
    `checkd(m.lpval, 13);  // lpval = 12 + 1 = 13
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
