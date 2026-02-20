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
    // Update ctor_var_reset to check instead of making a constructor
    bit [3:0] m_lo = P;
    bit [93:0] m_mid = '1;  // Wide
    bit [3:0] m_hi;
  } s_t;
  s_t s;

  initial begin
    $display("%p", s);
    `checkh(s.m_lo, 4'h5);
    `checkh(s.m_mid, ~94'h0);
    `checkh(s.m_hi, 4'h0);
    s.m_mid = 94'ha;
    s.m_hi = 4'hb;
    $display("%p", s);
    `checkh(s.m_lo, 4'h5);
    `checkh(s.m_mid, 94'ha);
    `checkh(s.m_hi, 4'hb);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
