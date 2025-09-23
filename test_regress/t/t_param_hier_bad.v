// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  function int pkg_func();
    return 1;
  endfunction
endpackage

module sub #(
    parameter int X = 1
) ();

  localparam int Y = X;
  localparam int Z = X;

  function int sub_func();
    return 1;
  endfunction

endmodule

module t;
  localparam int MY_X = 2;

  sub #(.X(MY_X)) u_sub ();

  localparam int SUB_Y = u_sub.Y;  // <--- BAD: IEEE 1800-2023 6.20.2 no hierarchical

  localparam int SUB_FUNC = u_sub.sub_func();  // <--- BAD: IEEE 1800-2023 6.20.2 no hierarchical

  localparam int OK_FUNC = local_func();  // ok

  localparam int OK_PKG_FUNC = pkg::pkg_func();  // ok

  sub #(.X(block.block_func())) u_sub2 ();  // <--- BAD

  begin : block
    function int block_func();
      return 2;
    endfunction
  end

  function int local_func();
    return 2;
  endfunction

  initial begin
    `checkd(SUB_Y, 1);
    `checkd(u_sub.X, 2);
    `checkd(u_sub.Y, 1);
    `checkd(u_sub.Z, 2);
    $finish;
  end

endmodule
