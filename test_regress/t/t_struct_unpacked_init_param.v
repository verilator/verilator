// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  parameter P = 4'h5;

  typedef struct {  // Must be unpacked -- existing error check
    bit [3:0] m_lo = P;
    bit [93:0] m_mid = '1;  // Wide
    bit [3:0] m_hi;
  } s_t;

  localparam s_t S = '{m_hi: 6};  // Not setting m_mid/m_hi

  localparam S_LO = S.m_lo;
  localparam S_HI = S.m_hi;

  initial begin
    `checkh(S.m_hi, 4'h6);
    `checkh(S_HI, 4'h6);

    `checkh(S.m_lo, 4'h5);
    `checkh(S_LO, 4'h5);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
