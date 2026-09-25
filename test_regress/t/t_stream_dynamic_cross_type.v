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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
