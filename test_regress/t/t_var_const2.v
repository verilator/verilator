// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

module t;
  const static int a1;
  const static int a2 = 0;

  const automatic int b1;
  const automatic int b2 = 0;

  initial begin
    const static int c1;
    const static int c2 = 0;

    const automatic int d1;
    const automatic int d2 = 0;
  end

  function static void tb_func1();
    const static int e1;
    const static int e2 = 0;

    const automatic int f1;
    const automatic int f2 = 0;
  endfunction

  function automatic void tb_func2();
    const static int g1;
    const static int g2 = 0;

    const automatic int h1;
    const automatic int h2 = 0;
  endfunction
endmodule
