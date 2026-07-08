// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks_w(width,gotv,expv) do begin \
  logic [(width)-1:0] got_check; \
  logic [(width)-1:0] exp_check; \
  got_check = (gotv); \
  exp_check = (expv); \
  if (got_check != exp_check) begin \
    $write("%%Error: %s:%0d:  got='%h' exp='%h'\n", `__FILE__,`__LINE__, got_check, exp_check); \
    `stop; \
  end \
end while(0);
`define checks(gotv,expv) `checks_w($bits(expv), gotv, expv)
module t;

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

  logic [128:0] wide129;

  initial begin
    byte byte_pkt[$];
    logic [15:0] sdata_pkt[$];
    int int_pkt[$];
    logic [63:0] qdata_pkt[$];
    logic [128:0] vlwide_pkt_129[$];//this is off by one to test edge cases
    logic [127:0] vlwide_pkt_128[$];
/* verilator lint_off ASCRANGE */
    logic [0:7] byte_pkt_rev[$];
    logic [0:15] sdata_pkt_rev[$];
    logic [0:31] int_pkt_rev[$];
    logic [0:63] qdata_pkt_rev[$];
    logic [0:128] vlwide_pkt_129_rev[$];//this is off by one to test edge cases
    logic [0:127] vlwide_pkt_128_rev[$];


    i_header = 12;
    i_len = 5;
    i_data = 11;
    i_crc = 42;
    i_char = 15;
    i_short = 16'hFF;
    #0; // this forces no-life
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

    `checks_w(128, {>>{byte_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks_w(128, {i_header,i_len,i_crc,i_data},{<<8{byte_pkt}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // //----------- SData QUEUE --------
    // sdata_pkt = {<<8{i_char}};
    //TODO This should compile
    // o_char = {{<<8{sdata_pkt}}}[7:0];
    // `checks(o_char,i_char);

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

    `checks_w(128, {>>{sdata_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
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

    `checks_w(128, {>>{int_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- QData QUEUE --------
    qdata_pkt = {<<8{i_header}};
    // o_header = {<<8{qdata_pkt}};
    //TODO This should compile
    // o_header = {{<<8{sdata_pkt}}}[32:0];
    // `checks(o_header,i_header);

    //test with QData
    qdata_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = qdata_pkt;
    `checks({i_header,i_len},{o_header,o_len});


    qdata_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = qdata_pkt;

    `checks_w(128, {>>{qdata_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- VLWide QUEUE --------
    // test with QData
    vlwide_pkt_129 = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = vlwide_pkt_129; //TODO this shouldn't compile lhs should not be smaller then rhs
    // `checks({i_header,i_len},{o_header,o_len});

    vlwide_pkt_129 = {<<8{i_header,i_len,i_crc,i_data}};

    /* verilator lint_off WIDTHEXPAND */
    wide129 = {<<8{i_header,i_len,i_crc,i_data}};
    `checks_w(129, {>>{vlwide_pkt_129}},wide129);
    /* verilator lint_on WIDTHEXPAND */

    //------------------------------- REVERSE ENDIAN ------------------------------
    //----------- CData QUEUE --------
    byte_pkt_rev = {<<8{i_char}};
    o_char = {<<8{byte_pkt_rev}};
    `checks(o_char,i_char);

    byte_pkt_rev = {<<8{i_short}};
    o_short = {<<8{byte_pkt_rev}};
    `checks(o_short,i_short);

    byte_pkt_rev = {<<8{i_header}};
    o_header = {<<8{byte_pkt_rev}};
    `checks(o_header,i_header);

    byte_pkt_rev = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = byte_pkt_rev;
    `checks({i_header,i_len},{o_header,o_len});

    byte_pkt_rev = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = byte_pkt_rev;

    `checks_w(128, {>>{byte_pkt_rev}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks_w(128, {i_header,i_len,i_crc,i_data},{<<8{byte_pkt_rev}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

        //----------- SData QUEUE --------
    sdata_pkt_rev = {<<8{i_short}};
    o_short = {<<8{sdata_pkt_rev}};
    `checks(o_short,i_short);

    sdata_pkt_rev = {<<8{i_header}};
    o_header = {<<8{sdata_pkt_rev}};
    `checks(o_header,i_header);

    //test with QData
    sdata_pkt_rev = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = sdata_pkt_rev;
    `checks({i_header,i_len},{o_header,o_len});

    sdata_pkt_rev = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = sdata_pkt_rev;

    `checks_w(128, {>>{sdata_pkt_rev}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- IData QUEUE --------
    int_pkt_rev = {<<8{i_header}};
    o_header = {<<8{int_pkt_rev}};
    `checks(o_header,i_header);

    //test with QData
    int_pkt_rev = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = int_pkt_rev;
    `checks({i_header,i_len},{o_header,o_len});

    int_pkt_rev = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = int_pkt_rev;

    `checks_w(128, {>>{int_pkt_rev}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- QData QUEUE --------

    //test with QData
    qdata_pkt_rev = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = qdata_pkt_rev;
    `checks({i_header,i_len},{o_header,o_len});


    qdata_pkt_rev = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = qdata_pkt_rev;

    `checks_w(128, {>>{qdata_pkt_rev}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- VLWide QUEUE --------

    vlwide_pkt_129_rev = {<<8{i_header,i_len,i_crc,i_data}};
    /* verilator lint_off WIDTHEXPAND */
    wide129 = {<<8{i_header,i_len,i_crc,i_data}};
    /* verilator lint_on WIDTHEXPAND */
    `checks_w(129, {>>{vlwide_pkt_129_rev}},wide129);

    // // -------------------- STREAMR ------------------------------------
    // //----------- CData QUEUE --------
    byte_pkt = {>>{i_header}};
    o_header = {>>{byte_pkt}};
    `checks(o_header,i_header);

    byte_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = byte_pkt;
    `checks_w(64, {>>{i_header,i_len}},{>>{o_header,o_len}});
    `checks({i_header,i_len},{o_header,o_len});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = byte_pkt;

    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- IData QUEUE --------
    int_pkt = {>>{i_header}};
    o_header = {>>{int_pkt}};
    `checks(o_header,i_header);
    `checks_w(32, o_header,{>>{int_pkt}});
    `checks_w(32, {>>{o_header}},{>>{int_pkt}});

    //test with QData
    int_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = int_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = int_pkt;

    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- QData QUEUE --------

    // test with QData
    qdata_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = qdata_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = qdata_pkt;

    `checks_w(128, {>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- VLWide QUEUE --------

    // test with QData
    vlwide_pkt_129 = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = vlwide_pkt_129;
    `checks({i_header,i_len},{o_header,o_len});


    vlwide_pkt_129 = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = vlwide_pkt_129;

    `checks_w(129, {>>{vlwide_pkt_129}},{>>{1'b0,i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //---------- into other queues ------
    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{int_pkt}};
    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{byte_pkt}};
    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{byte_pkt}};
    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    sdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{sdata_pkt}};
    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    sdata_pkt = {>>{byte_pkt}};
    `checks_w(128, {>>{sdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    qdata_pkt = {>>{byte_pkt}};
    `checks_w(128, {>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{qdata_pkt}};
    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{qdata_pkt}};
    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    qdata_pkt = {>>{int_pkt}};
    `checks_w(128, {>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{byte_pkt}};
    `checks_w(128, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{vlwide_pkt_128}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{byte_pkt}});
    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{int_pkt}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks_w(128, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{vlwide_pkt_128}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{int_pkt}});
    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{qdata_pkt}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks_w(128, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data,i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{qdata_pkt}};
    `checks_w(256, {i_header,i_len,i_crc,i_data,i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks_w(256, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data,i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data,i_header,i_len,i_crc}};
    vlwide_pkt_128 = {>>{qdata_pkt}};
    `checks_w(256, {32'h0,i_header,i_len,i_crc,i_data,i_header,i_len,i_crc},{>>{vlwide_pkt_128}});
    `checks_w(256, {>>{vlwide_pkt_128}},{>>{32'h0,i_header,i_len,i_crc,i_data,i_header,i_len,i_crc}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    qdata_pkt = {>>{vlwide_pkt_128}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks_w(128, {>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    $write("*-* All Finished *-*\n");
    $finish;

  end


endmodule
