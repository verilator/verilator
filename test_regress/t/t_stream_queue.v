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
  byte i_data[];
  int i_crc;

  int o_header;
  int o_len;
  byte o_data[];
  int o_crc;
  //this will not compile without -fno-life
  //full compiler command: ~/verilator/bin/verilator_bin_dbg --cc ../t_stream_queue.v -CFLAGS "-g -O0" --main --exe --build --timing --debug -fno-const -fno-life --gdbbt --dump-tree-addrids --decorations node --Mdir trace_objs/ > failed.txt
  initial begin
    //compiling with pkt[] breaks as well
    byte pkt[$];
    byte pkt2[$];
    i_header = 12;
    i_len = 5;
    i_data = new[5];
    i_crc = 42;

    //test with IData
    pkt = {<<8{i_header}};
    o_header = {<<8{pkt}};
    `checks(o_header,i_header);

    //test with QData
    pkt = {<<8{i_header,i_len}};
    {<<8{pkt2}} = pkt;
    `checks({>>{pkt2}},{<<8{i_header,i_len}});

    //test with QData not working
    pkt = {<<8{i_header,i_len}};

    //the left hand side should be two streaming operators this normally happens in the 035_const.tree step
    //however when queues are used it does not generate two streaming operators for this command only one.
    //look at t_stream_no_queue
    {<<8{o_header,o_len}} = pkt;
    `checks({i_header,i_len},{<<8{o_header,o_len}});

    pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{pkt2}} = pkt;
    //pkt2 has the correct data but we can not compare
    foreach(pkt2[i])
      $display("%h",pkt2[i]);
    // `checks({>>{pkt2}},{<<8{i_header,i_len,i_crc,i_data}}); //this will not compile correctly
    // `checks({>>{o_header,o_len,o_crc,o_data}} ,{<<8{i_header,i_len,i_crc,i_data}});

    // $display("%h o_header %h i_header",o_header,i_header);
    $finish;
  end


endmodule
