// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface class_if;
  class scoped_class;
    static function int fstatic();
      return 42;
    endfunction
    function int fnonstatic();
      return 43;
    endfunction
  endclass

  scoped_class class_inst;

  initial begin
    `checkh(scoped_class::fstatic(), 42);
    class_inst = new();
    `checkh(class_inst.fnonstatic(), 43);
  end
endinterface

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
  class_if class_if_inst();
  int v;

  initial begin
    v = 42;
    `checkh(v, 42);
    c::fstatic();
    classinst = new();
    classinst.fnonstatic();
    `checkh(v, 44);
    `checkh(class_if_inst.scoped_class.fstatic(), 42);
    $finish;
  end
endmodule
