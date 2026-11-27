// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Streams filling whole elements of a dynamic array or queue
  always @(posedge clk) begin
    bit [15:0] sb;
    byte unsigned d[];
    byte unsigned q[$];
    sb = crc[15:0];
    d = {>>byte{sb}};
    `checkh(d.size(), 2);
    `checkh(d[0], sb[15:8]);
    `checkh(d[1], sb[7:0]);
    q = {<<byte{sb}};
    `checkh(q.size(), 2);
    `checkh(q[0], sb[7:0]);
    `checkh(q[1], sb[15:8]);
  end

  // A stream not filling the last element is left-justified, zero-filled on the right
  always @(posedge clk) begin
    typedef logic [7:0] octet_t;
    logic [14:0] s15;
    logic [6:0] s7;
    logic [7:0] d[];
    octet_t q[$];
    int qi[$];
    bit [2:0] q3[$];
    s15 = crc[14:0];
    s7 = crc[20:14];
    d = {>>byte{s15}};
    `checkh(d.size(), 2);
    `checkh(d[0], s15[14:7]);
    `checkh(d[1], {s15[6:0], 1'b0});
    q = {<<4{s15}};
    `checkh(q.size(), 2);
    `checkh(q[0], {s15[3:0], s15[7:4]});
    `checkh(q[1], {s15[11:8], s15[14:12], 1'b0});
    qi = {>>{s15}};
    `checkh(qi.size(), 1);
    `checkh(qi[0], {s15, 17'b0});
    q3 = {>>{s7}};
    `checkh(q3.size(), 3);
    `checkh(q3[0], s7[6:4]);
    `checkh(q3[1], s7[3:1]);
    `checkh(q3[2], {s7[0], 2'b0});
  end

  // Wider streams
  always @(posedge clk) begin
    typedef byte unsigned bytes_t[$];
    logic [32:0] s33;
    logic [94:0] s95;
    logic [94:0] l95;
    logic [95:0] p96;
    byte unsigned d[];
    bytes_t q64;
    byte unsigned q[$];
    logic [69:0] w[];
    logic [68:0] x69;
    logic [99:0] x100;
    s33 = crc[40:8];
    s95 = {crc[30:0], ~crc};
    l95 = {<<8{s95}};
    p96 = {s95, 1'b0};
    d = {<<byte{s33}};
    `checkh(d.size(), 5);
    `checkh(d[0], s33[7:0]);
    `checkh(d[1], s33[15:8]);
    `checkh(d[2], s33[23:16]);
    `checkh(d[3], s33[31:24]);
    `checkh(d[4], {s33[32], 7'b0});
    q64 = {>>{crc}};
    `checkh(q64.size(), 8);
    for (int i = 0; i < 8; ++i) `checkh(q64[i], crc[63-8*i-:8]);
    q = {>>{s95}};
    `checkh(q.size(), 12);
    for (int i = 0; i < 12; ++i) `checkh(q[i], p96[95-8*i-:8]);
    w = {<<8{s95}};
    `checkh(w.size(), 2);
    `checkh(w[0], l95[94:25]);
    `checkh(w[1], {l95[24:0], 45'b0});
    {>>{x69}} = q;
    `checkh(x69, p96[95:27]);
    {>>{x100}} = w;
    `checkh(x100, {l95, 5'b0});
  end

  // Unpacking a dynamic array or queue takes its leftmost bits, packing into a wider value
  // left-justifies it
  always @(posedge clk) begin
    byte unsigned q[$];
    byte unsigned d[];
    logic [128:0] w[$];
    logic [39:0] l40[$];
    logic [6:0] a7;
    logic [7:0] a8;
    logic [11:0] a12;
    logic [3:0] n1, n2;
    byte unsigned u[2];
    logic [63:0] l64;
    logic [127:0] l128;
    logic [31:0] x32;
    logic [95:0] x96;
    q = '{crc[7:0], crc[15:8], crc[23:16]};
    d = '{crc[31:24], crc[39:32], crc[47:40]};
    w = '{{crc[0], crc, ~crc}};
    l40 = '{crc[39:0], crc[63:24]};
    {>>{a8}} = q;
    `checkh(a8, crc[7:0]);
    {>>{a12}} = q;
    `checkh(a12, {crc[7:0], crc[15:12]});
    {>>{a12}} = l40;
    `checkh(a12, crc[39:28]);
    {>>{a7}} = w;
    `checkh(a7, {crc[0], crc[63:58]});
    {>>{n1, n2}} = q;
    `checkh(n1, crc[7:4]);
    `checkh(n2, crc[3:0]);
    {>>{u}} = d;
    `checkh(u[0], crc[31:24]);
    `checkh(u[1], crc[39:32]);
    {>>{l64}} = w;
    `checkh(l64, {crc[0], crc[63:1]});
    {>>{l128}} = w;
    `checkh(l128, {crc[0], crc, ~crc[63:1]});
    x32 = {>>{q}};
    `checkh(x32, {crc[7:0], crc[15:8], crc[23:16], 8'h00});
    x32 = {<<8{q}};
    `checkh(x32, {crc[23:16], crc[15:8], crc[7:0], 8'h00});
    x32 = {<<16{q}};
    `checkh(x32, {crc[15:8], crc[23:16], crc[7:0], 8'h00});
    x96 = {<<8{q}};
    `checkh(x96, {crc[23:16], crc[15:8], crc[7:0], 72'h0});
  end

endmodule
