// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Ref args with a packed-array range-direction mismatch must be accepted.
// IEEE 1800-2023 6.22.2: packed types are equivalent by bit width, not range
// direction, so [15:0] and [0:15] are compatible for a ref port.

// verilator lint_off ASCRANGE

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  function automatic void fill_desc(ref logic [3:0][7:0] arr);
`ifdef T_NOINLINE
    // verilator no_inline_task
`endif
    arr = 32'hdead_beef;
  endfunction

  function automatic void fill_asc(ref logic [0:3][7:0] arr);
`ifdef T_NOINLINE
    // verilator no_inline_task
`endif
    arr = 32'hdead_beef;
  endfunction

  // Inner (basic-dtype) range-direction mismatch.
  function automatic void fill_inner_desc(ref logic [1:0][15:0] arr);
`ifdef T_NOINLINE
    // verilator no_inline_task
`endif
    arr = 32'hdead_beef;
  endfunction

  function automatic void fill_inner_asc(ref logic [1:0][0:15] arr);
`ifdef T_NOINLINE
    // verilator no_inline_task
`endif
    arr = 32'hdead_beef;
  endfunction

  logic [3:0][7:0]  a;   // descending outer
  logic [0:3][7:0]  b;   // ascending outer
  logic [1:0][15:0] c;   // descending inner
  logic [1:0][0:15] d;   // ascending inner

  initial begin
    // Outer-dimension direction mismatch
    a = '0; fill_desc(a);        `checkh(a, 32'hdead_beef);
    b = '0; fill_desc(b);        `checkh(b, 32'hdead_beef);
    a = '0; fill_asc(a);         `checkh(a, 32'hdead_beef);
    b = '0; fill_asc(b);         `checkh(b, 32'hdead_beef);
    // Inner-dimension direction mismatch
    c = '0; fill_inner_desc(c);  `checkh(c, 32'hdead_beef);
    d = '0; fill_inner_desc(d);  `checkh(d, 32'hdead_beef);
    c = '0; fill_inner_asc(c);   `checkh(c, 32'hdead_beef);
    d = '0; fill_inner_asc(d);   `checkh(d, 32'hdead_beef);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
