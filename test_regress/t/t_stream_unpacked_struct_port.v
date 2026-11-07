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

module t (
    input clk
);

  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } inner_t;

  // Unpacked struct, $bits == 40
  typedef struct {
    inner_t x;
    logic [15:0] c;
    logic [7:0] d;
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
  arr_t arr_r;
  arr_t arr_l;
  producer #(
      .W(OW)
  ) u_r (
      .din(src),
      .dout({>>{out_r}})
  );
  producer #(
      .W(OW)
  ) u_l (
      .din(src),
      .dout({<<8{out_l}})
  );
  producer #(
      .W(OW)
  ) u_ar (
      .din(src),
      .dout({>>{arr_r}})
  );
  producer #(
      .W(OW)
  ) u_al (
      .din(src),
      .dout({<<8{arr_l}})
  );

  // Constant function and system function indices remain valid inside output streams.
  function automatic int constant_index();
    return 1;
  endfunction
  logic [14:1] selected_r;
  logic [14:1] selected_l;
  producer #(
      .W(14)
  ) u_selected_r (
      .din(crc[13:0]),
      .dout({>>{selected_r[14:8], selected_r[constant_index() +: 7]}})
  );
  // Nest the right stream inside the left stream to check recursive destinations.
  producer #(
      .W(14)
  ) u_selected_l (
      .din(crc[13:0]),
      .dout({<<7{{>>{selected_l[14:8], selected_l[$clog2(2) +: 7]}}}})
  );

  // Inputs may select packed bits dynamically. Unpacked variable output indices may
  // also vary, and selections within those indices are reads, not destinations.
  wire [31:0] row = 1 + int'(crc[17:16]) % 3;
  wire [31:0] input_base = 7 * int'(crc[15:14]);
  logic [6:0] variable_pad [3:1];
  producer #(
      .W(7)
  ) u_variable (
      .din({<<{crc[input_base +: 7]}}),
      .dout({>>{variable_pad[1 + int'(crc[17:16]) % 3]}})
  );
  logic [2:1] constant_bit_pad;
  producer #(
      .W(1)
  ) u_constant_bit (
      .din({<<{crc[crc[5:0]]}}),
      .dout({>>{constant_bit_pad[constant_index()]}})
  );

  // Reference: plain packed port + separate streaming unpack assign.
  wire [OW-1:0] pack_r;
  wire [OW-1:0] pack_l;
  order_t ref_r, ref_l;
  producer #(
      .W(OW)
  ) u_pr (
      .din(src),
      .dout(pack_r)
  );
  producer #(
      .W(OW)
  ) u_pl (
      .din(src),
      .dout(pack_l)
  );
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
      `checkh(selected_r, crc[13:0]);
      `checkh(selected_l[14:8], crc[6:0]);
      `checkh(selected_l[7:1], crc[13:7]);
      `checkh(constant_bit_pad[1], crc[crc[5:0]]);
      for (int i = 0; i < 7; ++i) begin
        `checkh(variable_pad[row][6-i], crc[input_base+i]);
      end
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
    input logic [W-1:0] din,
    output logic [W-1:0] dout
);
  assign dout = din;
endmodule
