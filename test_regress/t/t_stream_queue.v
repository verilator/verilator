// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int i_header;
  int i_len;
  byte i_data[];
  int i_crc;

  int o_header;
  int o_len;
  byte o_data[];
  int o_crc;

  initial begin
    byte pkt[$];

    i_header = 12;
    i_len = 5;
    i_data = new[5];
    i_crc = 42;

    pkt = {<<8{i_header, i_len, i_data, i_crc}};

    {<<8{o_header, o_len, o_data, o_crc}} = pkt;

    $finish;
  end

endmodule
