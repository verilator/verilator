// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Verilator Authors.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit source_bits[];
  int unsigned destination_words[];

  initial begin
    source_bits = new[37];
    source_bits[0] = 1;
    source_bits[2] = 1;
    source_bits[5] = 1;
    source_bits[31] = 1;
    source_bits[36] = 1;

    destination_words = {>>{source_bits}};
    `checkh(destination_words.size(), 2);
    `checkh(destination_words[0], 32'ha4000001);
    `checkh(destination_words[1], 32'h08000000);

    destination_words = {<<{source_bits}};
    `checkh(destination_words.size(), 2);
    `checkh(destination_words[0], 32'h84000001);
    `checkh(destination_words[1], 32'h28000000);

    begin
      // Queue streamed into dynamic arrays
      typedef byte byte_array_t[];
      byte source_q[$];
      byte_array_t destination_bytes;
      logic [11:0] destination_12[];
      logic [3:0] destination_4[];
      source_q = '{8'h12, 8'h34, 8'h56};
      destination_bytes = {>>{source_q}};
      `checkh(destination_bytes.size(), 3);
      `checkh(destination_bytes[0], 8'h12);
      `checkh(destination_bytes[2], 8'h56);
      destination_bytes = {<<8{source_q}};
      `checkh(destination_bytes.size(), 3);
      `checkh(destination_bytes[0], 8'h56);
      `checkh(destination_bytes[2], 8'h12);
      destination_12 = {>>{source_q}};
      `checkh(destination_12.size(), 2);
      `checkh(destination_12[0], 12'h123);
      `checkh(destination_12[1], 12'h456);
      destination_4 = {>>{source_q}};
      `checkh(destination_4.size(), 6);
      foreach (destination_4[i]) `checkh(destination_4[i], 4'(i + 1));
      destination_4 = {<<4{source_q}};
      `checkh(destination_4.size(), 6);
      foreach (destination_4[i]) `checkh(destination_4[i], 4'(6 - i));
      destination_words = {<<4{source_q}};
      `checkh(destination_words.size(), 1);
      `checkh(destination_words[0], 32'h65432100);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
