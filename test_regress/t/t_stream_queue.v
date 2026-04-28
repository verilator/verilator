// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%h' exp='%h'\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0);
module t;
  logic clk;

  logic [7:0] i_char;
  logic [15:0] i_short;
  int i_header;
  int i_len;
  int i_data;
  int i_crc;

  logic [7:0] o_char;
  logic [15:0] o_short;
  int o_header;
  int o_len;
  int o_data;
  int o_crc;

  initial begin
    byte byte_pkt[$];
    logic [15:0] sdata_pkt[$];
    int int_pkt[$];
    logic [63:0] qdata_pkt[$];
    logic [127:0] vlwide_pkt_129[$];//this is off by one to test edge cases
    logic [127:0] vlwide_pkt_128[$];


    i_header = 12;
    i_len = 5;
    i_data = 11;
    i_crc = 42;
    i_char = 15;
    i_short = 16'hFF;
    #5; // this forces no-life
    //TODO make this work with V3Life
    //-------------------- STREAML ------------------------------------
    //----------- CData QUEUE --------
    byte_pkt = {<<8{i_char}};
    o_char = {<<8{byte_pkt}};
    `checks(o_char,i_char);

    byte_pkt = {<<8{i_short}};
    o_short = {<<8{byte_pkt}};
    `checks(o_short,i_short);

    byte_pkt = {<<8{i_header}};
    o_header = {<<8{byte_pkt}};
    `checks(o_header,i_header);

    byte_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = byte_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    byte_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = byte_pkt;

    `checks({>>{byte_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({i_header,i_len,i_crc,i_data},{<<8{byte_pkt}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- SData QUEUE --------
    sdata_pkt = {<<8{i_char}};
    o_char = {<<8{sdata_pkt}};
    `checks(o_char,i_char);

    sdata_pkt = {<<8{i_short}};
    o_short = {<<8{sdata_pkt}};
    `checks(o_short,i_short);

    sdata_pkt = {<<8{i_header}};
    o_header = {<<8{sdata_pkt}};
    `checks(o_header,i_header);

    //test with QData
    sdata_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = sdata_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    sdata_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = sdata_pkt;

    `checks({>>{sdata_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- IData QUEUE --------
    int_pkt = {<<8{i_header}};
    o_header = {<<8{int_pkt}};
    `checks(o_header,i_header);

    //test with QData
    int_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = int_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    int_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = int_pkt;

    `checks({>>{int_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- QData QUEUE --------
    qdata_pkt = {<<8{i_char}};
    o_char = {<<8{qdata_pkt}};
    `checks(o_char,i_char);

    qdata_pkt = {<<8{i_short}};
    o_short = {<<8{qdata_pkt}};
    `checks(o_short,i_short);

    qdata_pkt = {<<8{i_header}};
    o_header = {<<8{qdata_pkt}};
    `checks(o_header,i_header);

    //test with QData
    qdata_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = qdata_pkt;
    `checks({i_header,i_len},{o_header,o_len});


    qdata_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = qdata_pkt;

    `checks({>>{qdata_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- VLWide QUEUE --------
    vlwide_pkt_129 = {<<8{i_char}};
    o_char = {<<8{vlwide_pkt_129}};
    `checks(o_char,i_char);

    vlwide_pkt_129 = {<<8{i_short}};
    o_short = {<<8{vlwide_pkt_129}};
    `checks(o_short,i_short);

    vlwide_pkt_129 = {<<8{i_header}};
    o_header = {<<8{vlwide_pkt_129}};
    `checks(o_header,i_header);

    // test with QData
    vlwide_pkt_129 = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = vlwide_pkt_129;
    `checks({i_header,i_len},{o_header,o_len});

    vlwide_pkt_129 = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = vlwide_pkt_129;

    `checks({>>{vlwide_pkt_129}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // -------------------- STREAMR ------------------------------------
    //----------- CData QUEUE --------
    byte_pkt = {>>{i_header}};
    o_header = {>>{byte_pkt}};
    `checks(o_header,i_header);

    byte_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = byte_pkt;
    `checks({>>{i_header,i_len}},{>>{o_header,o_len}});
    `checks({i_header,i_len},{o_header,o_len});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = byte_pkt;

    `checks({>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- IData QUEUE --------
    int_pkt = {>>{i_header}};
    o_header = {>>{int_pkt}};
    `checks(o_header,i_header);
    `checks(o_header,{>>{int_pkt}});
    `checks({>>{o_header}},{>>{int_pkt}});



    //test with QData
    int_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = int_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = int_pkt;

    `checks({>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- QData QUEUE --------
    qdata_pkt = {>>{i_header}};
    o_header = {>>{qdata_pkt}};
    `checks(o_header,i_header);
    `checks(o_header,{>>{qdata_pkt}});

    // test with QData
    qdata_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = qdata_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = qdata_pkt;

    `checks({>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- VLWide QUEUE --------
    vlwide_pkt_129 = {>>{i_char}};
    o_char = {>>{vlwide_pkt_129}};
    `checks(o_char,i_char);

    vlwide_pkt_129 = {>>{i_short}};
    o_short = {>>{vlwide_pkt_129}};
    `checks(o_short,i_short);

    vlwide_pkt_129 = {>>{i_header}};
    o_header = {>>{vlwide_pkt_129}};
    `checks(o_header,i_header);

    // test with QData
    vlwide_pkt_129 = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = vlwide_pkt_129;
    `checks({i_header,i_len},{o_header,o_len});


    vlwide_pkt_129 = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = vlwide_pkt_129;

    `checks({>>{vlwide_pkt_129}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //---------- into other queues ------
    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{int_pkt}};
    `checks({>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{byte_pkt}};
    `checks({>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    qdata_pkt = {>>{byte_pkt}};
    `checks({>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{qdata_pkt}};
    `checks({>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{byte_pkt}};
    `checks({>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{vlwide_pkt_128}};
    `checks({i_header,i_len,i_crc,i_data},{>>{byte_pkt}});
    `checks({>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{int_pkt}};
    `checks({i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks({>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{vlwide_pkt_128}};
    `checks({i_header,i_len,i_crc,i_data},{>>{int_pkt}});
    `checks({>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{qdata_pkt}};
    `checks({i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks({>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    qdata_pkt = {>>{vlwide_pkt_128}};
    `checks({i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks({>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});


  end


endmodule
