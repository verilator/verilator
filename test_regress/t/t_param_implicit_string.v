// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  sub u_sub ();
endmodule

module sub #(
    parameter INDEX = 4096
);
  parameter STRG = $sformatf("stringed[%0d]", INDEX);
  initial begin
    `checks(STRG, "stringed[4096]");
    $finish;
  end
endmodule
