// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Martin Velay
// SPDX-License-Identifier: CC0-1.0

module t;
  string s = "hello";
  bit [39:0] b40;
  byte bq[$];
  byte bd[];

  initial begin
    {>>{b40}} = s;
    {>>{bq}} = s;
    {<<8{bd}} = s;
    $finish;
  end
endmodule
