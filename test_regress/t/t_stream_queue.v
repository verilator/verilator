// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%h' exp='%h'\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0);
module t;

  int i_header;
  int i_len;
  int i_data;
  int i_crc;

  int o_header;
  int o_len;
  int o_data;
  int o_crc;
  //this will not compile without -fno-life
  //full compiler command: ~/verilator/bin/verilator_bin_dbg --cc ../t_stream_queue.v -CFLAGS "-g -O0" --main --exe --build --timing --debug -fno-const -fno-life --gdbbt --dump-tree-addrids --decorations node --Mdir trace_objs/ > failed.txt
  initial begin
    byte byte_pkt[$];
    int int_pkt[$];
    i_header = 12;
    i_len = 5;
    i_data = 11;
    i_crc = 42;
    // #5;
    //-------------------- STREAML ------------------------------------
    //test with IData
    byte_pkt = {<<8{i_header}};
    o_header = {<<8{byte_pkt}};
    `checks(o_header,i_header);

    //test with QData
    byte_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = byte_pkt;
    $display("%h %h",{i_header,i_len},{o_header,o_len});

    byte_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = byte_pkt;

    `checks({>>{byte_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- INT QUEUE --------
    int_pkt = {<<8{i_header}};
    o_header = {<<8{int_pkt}};
    `checks(o_header,i_header);

    //test with QData
    int_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = int_pkt;
    $display("%h %h",{i_header,i_len},{o_header,o_len});

    int_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = int_pkt;

    `checks({>>{int_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //-------------------- STREAMR ------------------------------------
    // byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    // foreach(byte_pkt[i])
    //   $display("%h",byte_pkt[i]);
    // $display("%h o_header %h i_header",o_header,i_header);
    // $finish;
  end


endmodule
