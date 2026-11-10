// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

`define report_error(value) value = 1
`define report_warning(value) value = 1
`define report(value, severity = error ) `report_``severity(value)
`define spaced(text = " two words " ) text
// verilog_format: on

module t;
  bit default_value = 0;
  bit non_default_value = 0;
  bit no_value = 0;
  initial begin
    `report(default_value);
    `report(non_default_value, warning);
    `report(no_value,);

    `checkh(default_value, 1);
    `checkh(non_default_value, 1);
    `checkh(no_value, 1);
    `checkh(`spaced(), " two words ");
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
