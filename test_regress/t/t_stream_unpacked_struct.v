// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Ref. to IEEE 1800-2023 11.4.14, A.8.1

module t;

  `define checkh(gotv, expv) \
    do if ((gotv) !== (expv)) begin \
      $write("%%Error: %s:%0d: got='h%x exp='h%x\n", `__FILE__, `__LINE__, (gotv), (expv)); \
      $stop; \
    end while (0);

  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } packed_pair_t;

  typedef union packed {
    logic [7:0] byte_data;
    packed_pair_t pair;
  } packed_union_t;

  typedef struct {
    byte a;
    logic [3:0] b;
    packed_pair_t p;
  } simple_t;

  typedef struct {
    byte prefix;
    byte data[2];
    packed_pair_t p;
  } array_t;

  typedef struct {
    simple_t inner;
    byte tail[2];
  } nested_t;

  typedef struct {
    byte prefix;
    simple_t items[2];
    byte suffix;
  } struct_array_t;

  typedef struct {
    byte data[1:0];
  } descending_array_t;

  typedef struct {
    byte matrix[2][3];
  } matrix_array_t;

  typedef struct {
    logic [1:0][3:0] data[2];
  } mixed_array_t;

  typedef enum logic [2:0] {
    E0 = 3'd0,
    E5 = 3'd5
  } enum_t;

  typedef struct {
    enum_t e;
    logic [4:0] x;
  } enum_struct_t;

  typedef struct {
    byte tag;
    real r;
    realtime rt;
    real ra[2];
  } real_struct_t;

  typedef struct {
    packed_union_t u;
    byte tail;
  } packed_union_struct_t;

  simple_t simple;
  simple_t simple_out;
  simple_t simple_cont_out;
  array_t arrayed;
  array_t arrayed_out;
  nested_t nested;
  nested_t nested_out;
  struct_array_t struct_array;
  struct_array_t struct_array_out;
  descending_array_t descending;
  descending_array_t descending_out;
  matrix_array_t matrix_array;
  matrix_array_t matrix_array_out;
  mixed_array_t mixed_array;
  mixed_array_t mixed_array_out;
  simple_t simple_array[2];
  simple_t simple_array_out[2];
  enum_struct_t enum_struct;
  enum_struct_t enum_struct_out;
  real_struct_t real_struct;
  real_struct_t real_struct_out;
  packed_union_struct_t packed_union_struct;
  packed_union_struct_t packed_union_struct_out;

  logic [19:0] simple_bits;
  logic [31:0] wide_simple_bits;
  logic [31:0] array_bits;
  logic [35:0] nested_bits;
  logic [55:0] struct_array_bits;
  logic [15:0] descending_bits;
  logic [47:0] matrix_array_bits;
  logic [15:0] mixed_array_bits;
  logic [39:0] simple_array_bits;
  logic [31:0] byteswapped_bits;
  logic [7:0] enum_bits;
  logic [263:0] real_bits;
  logic [15:0] packed_union_bits;
  logic [11:0] narrow_bits;
  logic [19:0] simple_streaml_src;
  byte byte_array_out[2];

  assign {>>{simple_cont_out}} = 20'habcde;

  initial begin
    byteswapped_bits = {<<8{32'h11223344}};
    `checkh(byteswapped_bits, 32'h44332211);
    byteswapped_bits = {<<byte{32'h11223344}};
    `checkh(byteswapped_bits, 32'h44332211);

    {>>{simple_bits}} = 20'h13579;
    `checkh(simple_bits, 20'h13579);
    {<<4{simple_bits}} = 20'h12345;
    `checkh(simple_bits, 20'h54321);

    simple = '{8'h12, 4'ha, '{4'hb, 4'hc}};
    simple_bits = {>>{simple}};
    `checkh(simple_bits, 20'h12abc);
    /* verilator lint_off WIDTHEXPAND */
    wide_simple_bits = {>>{simple}};
    /* verilator lint_on WIDTHEXPAND */
    `checkh(wide_simple_bits, 32'h12abc000);
    simple_bits = {<<4{simple}};
    `checkh(simple_bits, 20'hcba21);

    {>>{simple_out}} = 20'h345de;
    `checkh(simple_out.a, 8'h34);
    `checkh(simple_out.b, 4'h5);
    `checkh(simple_out.p, 8'hde);
    `checkh(simple_cont_out.a, 8'hab);
    `checkh(simple_cont_out.b, 4'hc);
    `checkh(simple_cont_out.p, 8'hde);

    {<<4{simple_out}} = 20'h789ab;
    `checkh(simple_out.a, 8'hba);
    `checkh(simple_out.b, 4'h9);
    `checkh(simple_out.p, 8'h87);

    simple_out = {>>{20'hfedcb}};
    `checkh(simple_out.a, 8'hfe);
    `checkh(simple_out.b, 4'hd);
    `checkh(simple_out.p, 8'hcb);

    simple_out = {>>{simple}};
    `checkh(simple_out.a, 8'h12);
    `checkh(simple_out.b, 4'ha);
    `checkh(simple_out.p, 8'hbc);

    {>>{simple_out}} = simple;
    `checkh(simple_out.a, 8'h12);
    `checkh(simple_out.b, 4'ha);
    `checkh(simple_out.p, 8'hbc);

    if ($test$plusargs("t_stream_unpacked_struct_alt")) begin
      narrow_bits = 12'h123;
    end
    else begin
      narrow_bits = 12'habd;
    end
    /* verilator lint_off WIDTHEXPAND */
    simple_bits = {>>{narrow_bits}};
    /* verilator lint_on WIDTHEXPAND */
    `checkh(simple_bits, {narrow_bits, 8'h00});

    simple_out = {>>{narrow_bits}};
    `checkh(simple_out.a, narrow_bits[11:4]);
    `checkh(simple_out.b, narrow_bits[3:0]);
    `checkh(simple_out.p, 8'h00);

    {>>{simple_out}} = 24'habcdef;
    `checkh(simple_out.a, 8'hab);
    `checkh(simple_out.b, 4'hc);
    `checkh(simple_out.p, 8'hde);

    simple_out = {<<4{20'h13579}};
    `checkh(simple_out.a, 8'h97);
    `checkh(simple_out.b, 4'h5);
    `checkh(simple_out.p, 8'h31);

    simple_streaml_src = 20'h2468a;
    simple_out = {<<4{simple_streaml_src}};
    `checkh(simple_out.a, 8'ha8);
    `checkh(simple_out.b, 4'h6);
    `checkh(simple_out.p, 8'h42);

    {<<4{simple_out}} = simple_streaml_src;
    `checkh(simple_out.a, 8'ha8);
    `checkh(simple_out.b, 4'h6);
    `checkh(simple_out.p, 8'h42);

    {<<8{byte_array_out}} = 16'h1234;
    `checkh(byte_array_out[0], 8'h34);
    `checkh(byte_array_out[1], 8'h12);

    arrayed = '{8'h11, '{8'h22, 8'h33}, '{4'h4, 4'h5}};
    array_bits = {>>{arrayed}};
    `checkh(array_bits, 32'h11223345);
    array_bits = {<<8{arrayed}};
    `checkh(array_bits, 32'h45332211);

    {>>{arrayed_out}} = 32'haabbccdd;
    `checkh(arrayed_out.prefix, 8'haa);
    `checkh(arrayed_out.data[0], 8'hbb);
    `checkh(arrayed_out.data[1], 8'hcc);
    `checkh(arrayed_out.p, 8'hdd);

    nested = '{'{8'h12, 4'ha, '{4'hb, 4'hc}}, '{8'h34, 8'h56}};
    nested_bits = {>>{nested}};
    `checkh(nested_bits, 36'h12abc3456);

    {>>{nested_out}} = 36'h6543210fe;
    `checkh(nested_out.inner.a, 8'h65);
    `checkh(nested_out.inner.b, 4'h4);
    `checkh(nested_out.inner.p, 8'h32);
    `checkh(nested_out.tail[0], 8'h10);
    `checkh(nested_out.tail[1], 8'hfe);

    struct_array.prefix = 8'haa;
    struct_array.items[0] = '{8'h12, 4'h3, '{4'h4, 4'h5}};
    struct_array.items[1] = '{8'h67, 4'h8, '{4'h9, 4'ha}};
    struct_array.suffix = 8'hbb;
    struct_array_bits = {>>{struct_array}};
    `checkh(struct_array_bits, 56'haa123456789abb);

    {>>{struct_array_out}} = 56'hccdef0123456dd;
    `checkh(struct_array_out.prefix, 8'hcc);
    `checkh(struct_array_out.items[0].a, 8'hde);
    `checkh(struct_array_out.items[0].b, 4'hf);
    `checkh(struct_array_out.items[0].p, 8'h01);
    `checkh(struct_array_out.items[1].a, 8'h23);
    `checkh(struct_array_out.items[1].b, 4'h4);
    `checkh(struct_array_out.items[1].p, 8'h56);
    `checkh(struct_array_out.suffix, 8'hdd);

    descending = '{data: '{8'hcc, 8'hdd}};
    descending_bits = {>>{descending}};
    `checkh(descending_bits, 16'hccdd);

    {>>{descending_out}} = 16'h1234;
    `checkh(descending_out.data[1], 8'h12);
    `checkh(descending_out.data[0], 8'h34);

    matrix_array.matrix[0][0] = 8'h11;
    matrix_array.matrix[0][1] = 8'h22;
    matrix_array.matrix[0][2] = 8'h33;
    matrix_array.matrix[1][0] = 8'h44;
    matrix_array.matrix[1][1] = 8'h55;
    matrix_array.matrix[1][2] = 8'h66;
    matrix_array_bits = {>>{matrix_array}};
    `checkh(matrix_array_bits, 48'h112233445566);

    {>>{matrix_array_out}} = 48'haabbccddeeff;
    `checkh(matrix_array_out.matrix[0][0], 8'haa);
    `checkh(matrix_array_out.matrix[0][1], 8'hbb);
    `checkh(matrix_array_out.matrix[0][2], 8'hcc);
    `checkh(matrix_array_out.matrix[1][0], 8'hdd);
    `checkh(matrix_array_out.matrix[1][1], 8'hee);
    `checkh(matrix_array_out.matrix[1][2], 8'hff);

    mixed_array.data[0] = 8'hab;
    mixed_array.data[1] = 8'hcd;
    mixed_array_bits = {>>{mixed_array}};
    `checkh(mixed_array_bits, 16'habcd);

    {>>{mixed_array_out}} = 16'h1234;
    `checkh(mixed_array_out.data[0], 8'h12);
    `checkh(mixed_array_out.data[0][1], 4'h1);
    `checkh(mixed_array_out.data[0][0], 4'h2);
    `checkh(mixed_array_out.data[1], 8'h34);
    `checkh(mixed_array_out.data[1][1], 4'h3);
    `checkh(mixed_array_out.data[1][0], 4'h4);

    simple_array[0] = '{8'h12, 4'ha, '{4'hb, 4'hc}};
    simple_array[1] = '{8'h34, 4'hd, '{4'he, 4'hf}};
    simple_array_bits = {>>{simple_array}};
    `checkh(simple_array_bits, 40'h12abc34def);

    {>>{simple_array_out}} = 40'h567899abcd;
    `checkh(simple_array_out[0].a, 8'h56);
    `checkh(simple_array_out[0].b, 4'h7);
    `checkh(simple_array_out[0].p, 8'h89);
    `checkh(simple_array_out[1].a, 8'h9a);
    `checkh(simple_array_out[1].b, 4'hb);
    `checkh(simple_array_out[1].p, 8'hcd);

    enum_struct = '{E5, 5'ha};
    enum_bits = {>>{enum_struct}};
    `checkh(enum_bits, 8'haa);

    {>>{enum_struct_out}} = 8'h71;
    `checkh(enum_struct_out.e, 3'h3);
    `checkh(enum_struct_out.x, 5'h11);

    real_struct.tag = 8'h42;
    real_struct.r = 1.0;
    real_struct.rt = 3.0;
    real_struct.ra[0] = 4.0;
    real_struct.ra[1] = 5.0;
    real_bits = {>>{real_struct}};
    `checkh(real_bits,
            {8'h42, $realtobits(1.0), $realtobits(3.0), $realtobits(4.0), $realtobits(5.0)});

    {>>{real_struct_out}}
        = {8'h99, $realtobits(2.0), $realtobits(6.0), $realtobits(7.0), $realtobits(8.0)};
    `checkh(real_struct_out.tag, 8'h99);
    `checkh($realtobits(real_struct_out.r), $realtobits(2.0));
    `checkh($realtobits(real_struct_out.rt), $realtobits(6.0));
    `checkh($realtobits(real_struct_out.ra[0]), $realtobits(7.0));
    `checkh($realtobits(real_struct_out.ra[1]), $realtobits(8.0));

    packed_union_struct.u.byte_data = 8'hbe;
    packed_union_struct.tail = 8'hef;
    packed_union_bits = {>>{packed_union_struct}};
    `checkh(packed_union_bits, 16'hbeef);

    {>>{packed_union_struct_out}} = 16'hcafe;
    `checkh(packed_union_struct_out.u.byte_data, 8'hca);
    `checkh(packed_union_struct_out.tail, 8'hfe);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
