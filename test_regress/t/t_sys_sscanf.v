// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  localparam int unsigned XLEN = 32;

  string pkt;
  int unsigned idx;
  logic [XLEN-1:0] val;
  int code;

  initial begin
    // All digits after % is to get line coverage in verilated.cpp
    code = $sscanf("P20=4cff0000", "P%h=%80123456789h", idx, val);
    `checkh(code, 2);
    `checkh(idx, 32'h20);
    `checkh(val, 32'h4cff0000);
    $finish;
  end

endmodule
