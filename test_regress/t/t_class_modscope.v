// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module m ();
  class c;
    static function void fstatic();
      `checkh(v, 42);
      v++;
    endfunction
    function void fnonstatic();
      `checkh(v, 43);
      v++;
    endfunction
  endclass

  c classinst;
  int v;

  initial begin
    v = 42;
    `checkh(v, 42);
    c::fstatic();
    classinst = new();
    classinst.fnonstatic();
    `checkh(v, 44);
    $finish;
  end
endmodule
