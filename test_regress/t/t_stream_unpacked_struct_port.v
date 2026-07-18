// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Ref. to IEEE 1800-2023 11.4.14
//
// A streaming concatenation used as the lvalue of a module output-port
// connection, targeting an unpacked struct.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t(  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } inner_t;

  // Unpacked struct, $bits == 40
  typedef struct {
    inner_t      x;
    logic [15:0] c;
    logic [7:0]  d;
  } order_t;

  // Unpacked array, also $bits == 40 (so producer width OW is shared).
  typedef byte arr_t[5];

  localparam int OW = $bits(order_t);

  integer cyc = 0;
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;
  wire [OW-1:0] src = crc[OW-1:0];

  // Path under test: streaming concat as an output-port lvalue, into an
  // unpacked struct (needs CvtPackedToArray) and an unpacked array (does not).
  order_t out_r;  // right-stream {>>{}}
  order_t out_l;  // left-stream  {<<8{}}
  arr_t   arr_r;
  arr_t   arr_l;
  producer #(.W(OW)) u_r (.din(src), .dout({>>{out_r}}));
  producer #(.W(OW)) u_l (.din(src), .dout({<<8{out_l}}));
  producer #(.W(OW)) u_ar (.din(src), .dout({>>{arr_r}}));
  producer #(.W(OW)) u_al (.din(src), .dout({<<8{arr_l}}));

  // Reference: plain packed port + separate streaming unpack assign.
  wire [OW-1:0] pack_r;
  wire [OW-1:0] pack_l;
  order_t ref_r, ref_l;
  producer #(.W(OW)) u_pr (.din(src), .dout(pack_r));
  producer #(.W(OW)) u_pl (.din(src), .dout(pack_l));
  assign ref_r = {>>{pack_r}};
  assign ref_l = {<<8{pack_l}};

  // Packed views (streaming into a packed wire is the legal direction) so the
  // checks compare plain vectors rather than unpacked structs/arrays.
  wire [OW-1:0] out_r_bits = {>>{out_r}};
  wire [OW-1:0] out_l_bits = {<<8{out_l}};
  wire [OW-1:0] arr_r_bits = {>>{arr_r}};
  wire [OW-1:0] arr_l_bits = {<<8{arr_l}};
  wire [OW-1:0] ref_r_bits = {>>{ref_r}};
  wire [OW-1:0] ref_l_bits = {<<8{ref_l}};

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc > 1) begin
      // The target has a real driver (not folded to 0) and round-trips.
      `checkh(out_r_bits, src);
      `checkh(out_l_bits, src);
      `checkh(arr_r_bits, src);
      `checkh(arr_l_bits, src);
      // Output-port streaming lvalue matches the reference unpack.
      `checkh(out_r_bits, ref_r_bits);
      `checkh(out_l_bits, ref_l_bits);
      if (out_r !== ref_r) begin
        $write("%%Error: %s:%0d: out_r struct mismatch\n", `__FILE__, `__LINE__);
        $stop;
      end
      if (out_l !== ref_l) begin
        $write("%%Error: %s:%0d: out_l struct mismatch\n", `__FILE__, `__LINE__);
        $stop;
      end
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module producer #(
    parameter int W = 1
) (
    input  logic [W-1:0] din,
    output logic [W-1:0] dout
);
  assign dout = din;
endmodule
