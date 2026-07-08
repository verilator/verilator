// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
  import "DPI-C" function string func(input string arg) /*verilator dpi_c_decl "char* func(const char*)"*/;
  import "DPI-C" function string func_with_specifier(input string arg) /*verilator dpi_c_decl "char* func_with_specifier(const char*) throw()"*/;

  initial begin
    `checks(func("arg"), "abc");
    `checks(func_with_specifier("arg"), "efd");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
