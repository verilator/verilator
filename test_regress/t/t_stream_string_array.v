// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  string qs[$];
  string as[];
  string s;
  task automatic stringOperands();
    s = {>>{qs}};
    if (s != "") $stop;

    s = {>>{as}};
    if (s != "") $stop;

    qs = '{"ab", "c", ""};
    s = {>>{qs}};
    if (s != "abc") $stop;

    as = new[3];
    as[0] = "abcd";
    as[2] = "ef";
    s = {>>{as}};
    if (s != "abcdef") $stop;
  endtask

  // Value of "A", not known at compile time
  function automatic logic [7:0] charA();
`ifdef VERILATOR
    return $c(8'h41);
`else
    return 8'h41;
`endif
  endfunction

  // Fixed-size unpacked operands
  typedef struct {
    logic [7:0] a;
    logic [7:0] b[2];
  } us_t;
  task automatic fixedUnpacked();
    logic [7:0] ua[2];
    logic [7:0] ud[1:0];
    logic [7:0] un[2:1];
    logic [7:0] u2[2:1][0:1];
    logic [7:0] u12[12];
    us_t us;
    logic [7:0] a;
    string str;
    a = charA();
    ua = '{a + 2, a + 3};
    str = {>>{ua}};
    `checks(str, "CD");
    str = {<<8{ua}};
    `checks(str, "DC");
    ud[1] = a + 2;
    ud[0] = a + 3;
    str = {>>{ud}};
    `checks(str, "CD");
    str = {<<8{ud}};
    `checks(str, "DC");
    un[2] = a + 1;
    un[1] = a + 2;
    str = {>>{un}};
    `checks(str, "BC");
    u2 = '{'{a, a + 1}, '{a + 2, a + 3}};
    str = {>>{u2}};
    `checks(str, "ABCD");
    foreach (u12[i]) u12[i] = a + 8'(i);
    str = {>>{u12}};
    `checks(str, "ABCDEFGHIJKL");
    us.a = a + 4;
    us.b = '{a + 5, a + 6};
    str = {>>{us}};
    `checks(str, "EFG");
    str = {<<8{us}};
    `checks(str, "GFE");
  endtask

  // Queue and dynamic array operands
  typedef byte bqt_t[$];
  typedef enum logic [7:0] {
    EA = 8'h41,
    EB = 8'h42
  } e_t;
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } ps_t;
  task automatic queueOperands();
    byte bq[$];
    byte bbq[$:3];
    byte bd[];
    e_t eq[$];
    ps_t pq[$];
    int iq[$];
    logic [3:0] nq[$];
    logic [71:0] wq[$];
    logic [64:0] vq[$];
    bqt_t bqt;
    logic [7:0] a;
    string str;
    a = charA();
    bq = '{a, a + 1};
    str = {>>{bq}};
    `checks(str, "AB");
    str = {<<8{bq}};
    `checks(str, "BA");
    bbq = '{a + 1, a + 2};
    str = {>>{bbq}};
    `checks(str, "BC");
    str = {<<8{bbq}};
    `checks(str, "CB");
    bd = new[2];
    bd[0] = a + 4;
    bd[1] = a + 5;
    str = {>>{bd}};
    `checks(str, "EF");
    bd = new[3];
    bd[0] = a + 1;
    bd[1] = a + 2;
    bd[2] = a + 3;
    str = {<<8{bd}};
    `checks(str, "DCB");
    str = {<<16{bd}};
    `checks(str, "CDB");
    eq = '{e_t'(a), e_t'(a + 1)};
    str = {>>{eq}};
    `checks(str, "AB");
    str = {<<8{eq}};
    `checks(str, "BA");
    pq = '{'{a[7:4], a[3:0] + 4'd2}, '{a[7:4], a[3:0] + 4'd3}};
    str = {>>{pq}};
    `checks(str, "CD");
    str = {<<8{pq}};
    `checks(str, "DC");
    str = {<<4{pq}};
    `checks(str, "D4");
    iq = '{{a, a + 8'd1, a + 8'd2, a + 8'd3}};
    str = {>>{iq}};
    `checks(str, "ABCD");
    str = {<<8{iq}};
    `checks(str, "DCBA");
    nq = '{a[7:4], a[3:0], a[7:4], a[3:0] + 1};
    str = {>>{nq}};
    `checks(str, "AB");
    nq = '{a[3:0] + 1, a[7:4], a[3:0], a[7:4]};
    str = {<<4{nq}};
    `checks(str, "AB");
    wq = '{{a, 64'h4243444546474849}};
    str = {>>{wq}};
    `checks(str, "ABCDEFGHI");
    str = {<<8{wq}};
    `checks(str, "IHGFEDCBA");
    vq = '{{1'b0, a, 56'h42434445464748}, {1'b1, a + 8'd8, 56'h4a4b4c4d4e4f50}};
    str = {>>{vq}};
    `checks(str, "\x20\xa1\x21\xa2\x22\xa3\x23\xa4\x52\x52\x92\xd3\x13\x53\x93\xd4");
    str = {<<8{vq}};
    `checks(str, "PONMLKJI\x91\x8e\x8c\x8a\x88\x86\x84\x82");
    bq = '{a + 1, 8'h82};
    str = {<<{bq}};
    `checks(str, "AB");
    bqt = '{a + 2, a + 3};
    str = {>>{bqt}};
    `checks(str, "CD");
    // A slice at least as wide as the stream does not reorder it
    bq = '{a, a + 1};
    str = {<<32'hffffffff{bq}};
    `checks(str, "AB");
    bq.delete();
    str = {>>{bq}};
    `checks(str, "");
  endtask

  // A stream wider than 64 bits takes the whole string, queue or dynamic array
  task automatic wideStream();
    logic [127:0] w128;
    byte bq[$];
    byte bd[];
    logic [7:0] a;
    string str;
    a = charA();
    w128 = {a, 120'h42434445464748494a4b4c4d4e4f50};
    str = {>>{w128}};
    `checks(str, "ABCDEFGHIJKLMNOP");
    bq = {>>{w128}};
    `checkd(bq.size(), 16);
    `checkd(bq[15], 8'h50);
    bd = {>>{bq}};
    `checkd(bd.size(), 16);
    `checkd(bd[0], a);
  endtask

  // String queue operands, and a string typedef target
  typedef string str_t;
  typedef string sqt_t[$];
  task automatic stringQueueOperands();
    str_t sq[$];
    sqt_t sqt;
    string str;
    sq = '{"ab", "cd"};
    str = {>>{sq}};
    `checks(str, "abcd");
    sqt = '{"ef", "gh"};
    str = {>>{sqt}};
    `checks(str, "efgh");
    sq[0] = {>>{sqt}};
    `checks(sq[0], "efgh");
  endtask

  // The operand is evaluated once
  typedef logic [7:0] pair_t[2];
  int calls;
  function automatic pair_t getPair();
    logic [7:0] a;
    ++calls;
    a = charA();
    return '{a + 2, a + 3};
  endfunction
  function automatic us_t getStruct();
    us_t us;
    ++calls;
    us.a = charA() + 4;
    us.b = '{us.a + 1, us.a + 2};
    return us;
  endfunction
  task automatic singleEvaluation();
    string str;
    str = {>>{getPair()}};
    `checks(str, "CD");
    `checkd(calls, 1);
    str = {>>{getStruct()}};
    `checks(str, "EFG");
    `checkd(calls, 2);
  endtask

  localparam logic [11:0] P12 = 12'h142;
  // A string target is resized to whole bytes, and the stream is filled with zero bits on the
  // right (IEEE 1800-2023 11.4.14), as a string is a dynamic array of bytes (6.24.3). Streams
  // of 12 bits, 'h142, or 'h241 or 'h421 reversed in 4-bit or 8-bit slices, give "\x14\x20",
  // "\x24\x10" or "\x42\x10".
  task automatic padding();
    logic [11:0] p;
    logic [3:0] un3[3];
    logic [3:0] nq[$];
    logic [7:0] a;
    string str;
    a = charA();
    p = {a[7:4] - 4'd3, 8'h42};
    str = {>>{p}};
    `checks(str, "\x14\x20");
    str = {<<4{p}};
    `checks(str, "\x24\x10");
    un3 = '{a[7:4] - 4'd3, 4'h4, 4'h2};
    str = {>>{un3}};
    `checks(str, "\x14\x20");
    str = {<<4{un3}};
    `checks(str, "\x24\x10");
    nq = '{a[7:4] - 4'd3, 4'h4, 4'h2};
    str = {>>{nq}};
    `checks(str, "\x14\x20");
    str = {<<4{nq}};
    `checks(str, "\x24\x10");
    str = {<<8{nq}};
    `checks(str, "\x42\x10");
    str = {<<8{p}};
    `checks(str, "\x42\x10");
    // A cast is not a stream, so converts the value
    str = string'(p);
    `checks(str, "\x01\x42");
    // Constant operands
    str = {>>{12'h142}};
    `checks(str, "\x14\x20");
    str = {<<4{12'h142}};
    `checks(str, "\x24\x10");
    str = {>>{P12}};
    `checks(str, "\x14\x20");
    str = {>>{4'h4, 8'h14}};
    `checks(str, "A@");
    // 68 bits, the last 4 bits are 'h4
    nq.delete();
    for (int i = 0; i < 8; ++i) begin
      nq.push_back(a[7:4]);
      nq.push_back(a[3:0] + 4'(i));
    end
    nq.push_back(a[7:4]);
    str = {>>{nq}};
    `checks(str, "ABCDEFGH@");
    str = {<<4{nq}};
    `checks(str, "HGFEDCBA@");
  endtask

  // A fixed-size unpacked operand converts in a constant or always_comb context too
  localparam pair_t PAIR = '{8'h44, 8'h45};
  localparam string PAIR_STR = {>>{PAIR}};
  localparam us_t US = '{a: 8'h41, b: '{8'h42, 8'h43}};
  localparam string US_STR = {>>{US}};
  localparam logic [23:0] PACKED = 24'h414243;
  localparam string PACKED_STR = {>>{PACKED}};
  function automatic us_t defStruct();
    us_t us;
    us.a = 8'h44;
    us.b = '{8'h45, 8'h46};
    return us;
  endfunction
  string combStructStr;
  string combPairStr;
  always_comb combStructStr = {>>{defStruct()}};
  always_comb combPairStr = {>>{PAIR}};
  task automatic constantContexts();
    `checks(PAIR_STR, "DE");
    `checks(US_STR, "ABC");
    `checks(PACKED_STR, "ABC");
  endtask
  final begin
    `checks(combStructStr, "DEF");
    `checks(combPairStr, "DE");
  end

  initial begin
    stringOperands();
    fixedUnpacked();
    queueOperands();
    wideStream();
    stringQueueOperands();
    singleEvaluation();
    padding();
    constantContexts();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
