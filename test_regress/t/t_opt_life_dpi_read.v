// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define check(got,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: got='h%x exp='h%x\n", `__FILE__,`__LINE__, (got), (exp)); `stop; end while(0)
// verilog_format: on

module t;

  int dpiGet = 0;
  function automatic int getDpi();
    return dpiGet;
  endfunction
  export "DPI-C" function getDpi;
  import "DPI-C" context function int getViaDpi();  // calls getDpi()

  int tmp1, tmp2, tmp3;

  initial begin
    dpiGet = 13;
    tmp1 = getViaDpi();
    dpiGet = 14;
    tmp2 = getViaDpi();
    dpiGet = 15;
    tmp3 = getViaDpi();
    `check(tmp1, 13);
    `check(tmp2, 14);
    `check(tmp3, 15);
  end

endmodule
