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

  int dpiSet = 0;
  function automatic void setDpi(int value);
    dpiSet = value;
  endfunction
  export "DPI-C" function setDpi;
  import "DPI-C" context function void setViaDpi(int value);  // calls setDpi(value)

  initial begin
    dpiSet = 13;
    setViaDpi(14);
    `check(dpiSet, 14);
    dpiSet = 15;
    setViaDpi(16);
    `check(dpiSet, 16);
    dpiSet = 17;
    setViaDpi(18);
    `check(dpiSet, 18);
  end

endmodule
