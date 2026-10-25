// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Bit-stream casts of impure values in processes forked by a module (IEEE 1800-2023 6.24.3)

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  typedef struct {
    byte hi;
    byte lo;
  } halves_t;
  typedef byte bytes_t[2];

  int calls = 0;
  halves_t h;
  bytes_t b;

  function automatic shortint counted(shortint v);
    ++calls;
    return v;
  endfunction

  initial begin
    fork
      h = halves_t'(counted(16'h1234));
    join_none
    fork
      b = bytes_t'(counted(16'h5678));
    join_any
    #1;
    `checkh(h.hi, 8'h12);
    `checkh(h.lo, 8'h34);
    `checkh(b[0], 8'h56);
    `checkh(b[1], 8'h78);
    `checkd(calls, 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
