// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A select of a bit-stream cast to an unpacked struct. Selecting from a cast is an extension of
// the standard (IEEE 1800-2023 A.8.4) that other simulators and verilog_format reject.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  typedef struct {
    byte d[3:1];
    logic [6:0] t;
  } s31_t;

  always @(posedge clk) begin
    automatic int idx = 1 + cyc % 3;
    automatic byte b;
    b = s31_t'(crc[30:0]).d[idx];
    `checkh(b, crc[8*idx-1+:8]);
    b = s31_t'(crc[30:0]).d[3];
    `checkh(b, crc[30:23]);
  end

endmodule
