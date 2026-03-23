// DESCRIPTION: Verilator: Localparam with function call using type-parameterized interface param
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

interface ifc #(
    parameter type some_type
) ();
  localparam int PARAM = 1;
  localparam int TYPE_WIDTH = $bits(some_type);
endinterface

function automatic bit assert_func(bit value);
  if (!value) $fatal(2, "DEAD");
  return value;
endfunction

module mod (
    ifc i
);
  localparam bit lpbit = pkg::fn(i.PARAM);
  localparam bit test = assert_func(i.TYPE_WIDTH == 32);
endmodule

module t;
  ifc #(.some_type(int)) i ();
  mod m (.i);

  initial begin
    `checkd(m.lpbit, 1'b1);  // fn(1) returns 1 since 1 > 0
    `checkd(m.test, 1'b1);  // $bits(int) == 32, so assert_func(1) returns 1
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
