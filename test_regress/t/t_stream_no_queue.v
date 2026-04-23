// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0);
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
    int pkt32;
    logic [63:0] pkt64;
    i_header = 12;
    i_len = 5;
    i_data = new[5];
    i_crc = 42;

    //test with QData
    pkt64 = {<<8{i_header,i_len}};
    {<<8{o_header,i_len}} = pkt64;
    `checks(o_header,i_header);
    $display("%h o_header %h i_header",o_header,i_header);
    $finish;
  end


endmodule
