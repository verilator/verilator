// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A keyed assignment pattern without the leading apostrophe is non-standard (IEEE 1800-2023
// 10.9), but accepted as other simulators do, meaning the same as with the apostrophe

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
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Default only, as in the issue
  typedef struct packed {
    bit [7:0][31:0] m_irq_enable;
    bit [7:0][31:0] s_irq_enable;
  } plic_enable_t;
  initial begin
    plic_enable_t plic_enable;
    plic_enable = {default: '1};
    `checkh(plic_enable, {512{1'b1}});
    plic_enable = {default: '0};
    `checkh(plic_enable, '0);
  end

  // Member keys, in any order, and with a default
  typedef struct packed {
    logic [6:0] a;
    logic [14:0] b;
  } ab_t;
  always @(posedge clk) begin
    automatic ab_t v = {b: crc[14:0], a: crc[22:16]};
    `checkh(v, {crc[22:16], crc[14:0]});
    v = {b: crc[44:30], default: '1};
    `checkh(v, {7'h7f, crc[44:30]});
  end

  // Index keys, of unpacked arrays of each range direction, and of a packed vector
  always @(posedge clk) begin
    automatic logic [14:0] des[3:1] = {3: crc[14:0], default: crc[29:15]};
    automatic logic [14:0] asc[1:3] = {3: crc[14:0], default: crc[29:15]};
    automatic logic [8:0] vec = {0: crc[0], 8: crc[1], default: 1'b0};
    `checkh(des[3], crc[14:0]);
    `checkh(des[1], crc[29:15]);
    `checkh(asc[3], crc[14:0]);
    `checkh(asc[1], crc[29:15]);
    `checkh(vec, {crc[1], 7'h0, crc[0]});
  end

  // Type key
  typedef struct {
    int i;
    logic [6:0] s;
  } is_t;
  always @(posedge clk) begin
    automatic is_t v = {int: crc[31:0], default: crc[38:32]};
    `checkh(v.i, crc[31:0]);
    `checkh(v.s, crc[38:32]);
  end

  // Nested, also within a standard assignment pattern
  always @(posedge clk) begin
    automatic ab_t v[2];
    v = {1: {a: crc[6:0], default: '0}, 0: '{b: {default: crc[7]}, a: crc[14:8]}};
    `checkh(v[1], {crc[6:0], 15'h0});
    `checkh(v[0], {crc[14:8], {15{crc[7]}}});
  end

  // Parameter, continuous assignment, and function argument and return value
  localparam ab_t P = {a: 7'h5, b: 15'h1234};
  ab_t w;
  assign w = {a: crc[6:0], b: P.b};
  function automatic ab_t swap(input ab_t i);
    return {a: i.b[6:0], b: {8'h0, i.a}};
  endfunction
  always @(posedge clk) begin
    automatic ab_t s = swap({a: crc[6:0], b: crc[21:7]});
    `checkh(P, {7'h5, 15'h1234});
    `checkh(w, {crc[6:0], 15'h1234});
    `checkh(s, {crc[13:7], 8'h0, crc[6:0]});
  end

endmodule
