// DESCRIPTION: Verilator: Test pullup/pulldown with partial bus assigns
//
// This tests the case where:
// - A bus has some bits driven by pullup/pulldown through hierarchical modules
// - Other bits are driven by regular assigns (partial SEL)
// - The enable tracking must correctly handle the SEL assigns
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`default_nettype none

module pullup_mod (
    output HI
);
  pullup pullup0 (HI);
endmodule

module pulldown_mod (
    output LO
);
  pulldown pulldown0 (LO);
endmodule

module pull_pair_mod (
    output wire [1:0] pad
);
  pullup (pad[0]);
  pulldown (pad[1]);
endmodule

module mixed_pull_mod #(
    parameter int LEFT = 6,
    parameter int RIGHT = 0
) (
    inout wire [LEFT:RIGHT] pad
);
  for (genvar i = 0; i < $bits(pad); ++i) begin
    localparam int INDEX = LEFT < RIGHT ? RIGHT - i : RIGHT + i;
    // An asymmetric pattern catches reversed bit ordering.
    if (i == 0 || i == 2 || i == 5) begin
      pullup (pad[INDEX]);
    end else begin
      pulldown (pad[INDEX]);
    end
  end
endmodule

module whole_pull_mod (
    inout tri1 [6:0] pad
);
endmodule

module sparse_pull_mod (
    input wire enable,
    input wire [6:0] data,
    output wire [6:0] pad
);
  assign pad = enable ? data : 7'bz;
  pullup (pad[0]);
  pulldown (pad[5]);
  pullup (pad[6]);
endmodule

module pull_relay_mod (
    inout wire [2:0] high,
    inout wire [3:0] low
);
  // Reorder the child port so its per-bit pulls must be recorded and propagated again.
  mixed_pull_mod child (.pad({low, high}));
endmodule

module stream_pull_mod (
    input wire [6:0] enable,
    input wire [6:0] data,
    output wire [6:0] pad,
    output wire [6:0] observed
);
  assign observed = pad;
  for (genvar i = 0; i < 7; ++i) begin
    assign pad[i] = enable[i] ? data[i] : 1'bz;
    if (i == 0 || i == 2 || i == 5) begin
      pullup (pad[i]);
    end else begin
      pulldown (pad[i]);
    end
  end
endmodule

module wide_stream_pull_mod #(
    parameter int WIDTH = 4095
) (
    input wire enable,
    input wire [WIDTH-1:0] data,
    output wire [WIDTH-1:0] pad,
    output wire [WIDTH-1:0] observed
);
  assign pad = enable ? data : 'z;
  assign observed = pad;
  pullup (pad[0]);
  pullup (pad[WIDTH-2]);
  pulldown (pad[WIDTH-1]);
endmodule

module pull_bus_mod (
    input wire [3:0] in_value,
    output wire [7:0] out_value
);
  // Lower 4 bits driven by input (partial SEL assign)
  assign out_value[3:0] = in_value;

  // Upper 4 bits: alternating pullup/pulldown through hierarchical modules
  // out_value[4] = 1 (pullup)
  // out_value[5] = 0 (pulldown)
  // out_value[6] = 1 (pullup)
  // out_value[7] = 0 (pulldown)
  pullup_mod p0 (.HI(out_value[4]));
  pulldown_mod p1 (.LO(out_value[5]));
  pullup_mod p2 (.HI(out_value[6]));
  pulldown_mod p3 (.LO(out_value[7]));
endmodule

module t;
  reg [3:0] in_value;
  wire [7:0] out_value;

  pull_bus_mod dut (
      .in_value(in_value),
      .out_value(out_value)
  );

  initial begin
    // Test: Lower bits = 0xF
    in_value = 4'hF;
    #1;
    // Expected: 0x5F = 0101_1111
    // Bits [3:0] = F (from input)
    // Bit 4 = 1 (pullup), Bit 5 = 0 (pulldown)
    // Bit 6 = 1 (pullup), Bit 7 = 0 (pulldown)
    `checkh(out_value, 8'h5F);

    // Test: Lower bits = 0xA
    in_value = 4'hA;
    #1;
    // Expected: 0x5A = 0101_1010
    `checkh(out_value, 8'h5A);

    // Test: Lower bits = 0x0
    in_value = 4'h0;
    #1;
    // Expected: 0x50 = 0101_0000
    `checkh(out_value, 8'h50);

    wait (pull_done && concat_done && stream_done && wide_stream_done);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  logic pull_enable;
  logic [6:0] pull_data;
  bit pull_done = 0;

  // A per-bit pull must preserve the tri1 default in both packed range directions.
  tri1 [7:1] packed_default_pullup_desc;
  // verilator lint_off ASCRANGE
  tri1 [1:7] packed_default_pullup_asc;
  // verilator lint_on ASCRANGE
  pullup (packed_default_pullup_desc[3]);
  pullup (packed_default_pullup_asc[3]);
  assign packed_default_pullup_desc = pull_enable ? pull_data : 7'bz;
  assign packed_default_pullup_asc = pull_enable ? pull_data : 7'bz;

  // Likewise, preserve the tri0 default with a per-bit pulldown.
  tri0 [7:1] packed_default_pulldown_desc;
  // verilator lint_off ASCRANGE
  tri0 [1:7] packed_default_pulldown_asc;
  // verilator lint_on ASCRANGE
  pulldown (packed_default_pulldown_desc[3]);
  pulldown (packed_default_pulldown_asc[3]);
  assign packed_default_pulldown_desc = pull_enable ? pull_data : 7'bz;
  assign packed_default_pulldown_asc = pull_enable ? pull_data : 7'bz;

  initial begin
    for (int cyc = 0; cyc < 16; ++cyc) begin
      pull_enable = cyc[0];
      pull_data = 7'(cyc * 19);
      #1;
      `checkh(packed_default_pullup_desc, pull_enable ? pull_data : 7'h7f);
      `checkh(packed_default_pullup_asc, pull_enable ? pull_data : 7'h7f);
      `checkh(packed_default_pulldown_desc, pull_enable ? pull_data : 7'h00);
      `checkh(packed_default_pulldown_asc, pull_enable ? pull_data : 7'h00);
    end
    pull_done = 1;
  end

  // Preserve per-bit pulls when a port connects to separate scalar nets.
  wire concat_high, concat_low;
  pull_pair_mod scalar_concat (.pad({concat_high, concat_low}));

  // Nested concatenations distribute pulls to packed slices and scalar nets.
  wire [9:3] concat_packed;
  wire [5:1] concat_middle;
  wire concat_bit;
  logic concat_enable;
  logic [6:0] concat_data;
  bit concat_done = 0;
  mixed_pull_mod mixed_concat (.pad({concat_packed[9:7], {concat_middle[4:2], concat_bit}}));
  assign {concat_packed[9:7], concat_middle[4:2], concat_bit} = concat_enable ? concat_data : 7'bz;
  assign concat_packed[6:3] = concat_data[3:0];
  assign concat_middle[1] = concat_data[0];
  assign concat_middle[5] = ~concat_data[0];

  // An ascending child port connects to ascending and descending parent slices.
  // verilator lint_off ASCRANGE
  wire [3:9] concat_packed_asc;
  // verilator lint_on ASCRANGE
  wire [12:8] concat_middle_desc;
  wire concat_bit_asc;
  mixed_pull_mod #(.LEFT(2), .RIGHT(8)) mixed_concat_asc (
      .pad({concat_packed_asc[4:6], {concat_middle_desc[11:9], concat_bit_asc}})
  );
  assign {concat_packed_asc[4:6], concat_middle_desc[11:9], concat_bit_asc}
      = concat_enable ? concat_data : 7'bz;
  assign concat_packed_asc[3] = concat_data[0];
  assign concat_packed_asc[7:9] = concat_data[2:0];
  assign concat_middle_desc[8] = concat_data[0];
  assign concat_middle_desc[12] = ~concat_data[0];

  // A whole-port pull also applies to every part of a concatenated connection.
  wire [2:0] whole_high;
  wire [3:0] whole_low;
  whole_pull_mod whole_concat (.pad({whole_high, whole_low}));
  assign {whole_high, whole_low} = concat_enable ? concat_data : 7'bz;

  // Whole-port pulls also reach nonzero-based ascending variables in a concatenation.
  // verilator lint_off ASCRANGE
  wire [4:6] whole_high_asc;
  wire [9:12] whole_low_asc;
  // verilator lint_on ASCRANGE
  whole_pull_mod whole_concat_asc (.pad({whole_high_asc, whole_low_asc}));
  assign {whole_high_asc, whole_low_asc} = concat_enable ? concat_data : 7'bz;

  // The middle concatenation operand has no pulls; the low operand is only partly pulled.
  wire [10:9] sparse_high;
  wire [7:5] sparse_middle;
  wire [3:2] sparse_low;
  sparse_pull_mod sparse_concat (
      .enable(concat_enable),
      .data(concat_data),
      .pad({sparse_high, sparse_middle, sparse_low})
  );

  // Propagate pulls through two levels of concatenated and selected connections.
  wire [10:4] relay_high;
  wire [7:1] relay_low;
  wire relay_bit;
  pull_relay_mod relay_concat (
      .high(relay_high[8:6]),
      .low({relay_low[5:3], relay_bit})
  );
  assign {relay_high[8:6], relay_low[5:3], relay_bit} = concat_enable ? concat_data : 7'bz;

  // Selected connections apply pulls only within the normalized packed range.
  // Release the surrounding bits independently so a leaked pull cannot hide behind a driver.
  logic outside_enable;
  wire [13:3] selected_mixed;
  mixed_pull_mod mixed_slice (.pad(selected_mixed[13:7]));
  assign selected_mixed[13:7] = concat_enable ? concat_data : 7'bz;
  assign selected_mixed[6:3] = outside_enable ? concat_data[3:0] : 4'bz;
  wire [13:3] selected_whole;
  whole_pull_mod whole_slice (.pad(selected_whole[13:7]));
  assign selected_whole[13:7] = concat_enable ? concat_data : 7'bz;
  assign selected_whole[6:3] = outside_enable ? concat_data[3:0] : 4'bz;

  // Ascending selections leave the bits on both sides of the connection untouched.
  // verilator lint_off ASCRANGE
  wire [3:15] selected_mixed_asc;
  wire [3:15] selected_whole_asc;
  // verilator lint_on ASCRANGE
  mixed_pull_mod mixed_slice_asc (.pad(selected_mixed_asc[7:13]));
  whole_pull_mod whole_slice_asc (.pad(selected_whole_asc[7:13]));
  assign selected_mixed_asc[7:13] = concat_enable ? concat_data : 7'bz;
  assign selected_whole_asc[7:13] = concat_enable ? concat_data : 7'bz;
  assign selected_mixed_asc[3:6] = outside_enable ? concat_data[3:0] : 4'bz;
  assign selected_whole_asc[3:6] = outside_enable ? concat_data[3:0] : 4'bz;
  assign selected_mixed_asc[14:15] = outside_enable ? concat_data[1:0] : 2'bz;
  assign selected_whole_asc[14:15] = outside_enable ? concat_data[1:0] : 2'bz;

  initial begin
    for (int cyc = 0; cyc < 16; ++cyc) begin
      concat_enable = cyc[0];
      outside_enable = cyc[1];
      concat_data = 7'(cyc * 19);
      #1;
      `checkh({concat_high, concat_low}, 2'b01);
      `checkh({concat_packed[9:7], concat_middle[4:2], concat_bit},
              concat_enable ? concat_data : 7'h25);
      `checkh(concat_packed[6:3], concat_data[3:0]);
      `checkh(concat_middle[1], concat_data[0]);
      `checkh(concat_middle[5], ~concat_data[0]);
      `checkh({concat_packed_asc[4:6], concat_middle_desc[11:9], concat_bit_asc},
              concat_enable ? concat_data : 7'h25);
      `checkh(concat_packed_asc[3], concat_data[0]);
      `checkh(concat_packed_asc[7:9], concat_data[2:0]);
      `checkh(concat_middle_desc[8], concat_data[0]);
      `checkh(concat_middle_desc[12], ~concat_data[0]);
      `checkh({whole_high, whole_low}, concat_enable ? concat_data : 7'h7f);
      `checkh({whole_high_asc, whole_low_asc}, concat_enable ? concat_data : 7'h7f);
      if (concat_enable) begin
        `checkh({sparse_high, sparse_middle, sparse_low}, concat_data);
      end else begin
        `checkh(sparse_high, 2'b10);
        `checkh(sparse_middle === 3'bz, 1'b1);
        `checkh(sparse_low[3] === 1'bz, 1'b1);
        `checkh(sparse_low[2], 1'b1);
      end
      `checkh({relay_high[8:6], relay_low[5:3], relay_bit},
              concat_enable ? concat_data : 7'h54);
      `checkh(selected_mixed[13:7], concat_enable ? concat_data : 7'h25);
      `checkh(selected_whole[13:7], concat_enable ? concat_data : 7'h7f);
      `checkh(selected_mixed_asc[7:13], concat_enable ? concat_data : 7'h25);
      `checkh(selected_whole_asc[7:13], concat_enable ? concat_data : 7'h7f);
      `checkh(selected_mixed[6:3] === 4'bz, !outside_enable);
      `checkh(selected_whole[6:3] === 4'bz, !outside_enable);
      `checkh(selected_mixed_asc[3:6] === 4'bz, !outside_enable);
      `checkh(selected_whole_asc[3:6] === 4'bz, !outside_enable);
      `checkh(selected_mixed_asc[14:15] === 2'bz, !outside_enable);
      `checkh(selected_whole_asc[14:15] === 2'bz, !outside_enable);
      if (outside_enable) begin
        `checkh(selected_mixed[6:3], concat_data[3:0]);
        `checkh(selected_whole[6:3], concat_data[3:0]);
        `checkh(selected_mixed_asc[3:6], concat_data[3:0]);
        `checkh(selected_whole_asc[3:6], concat_data[3:0]);
        `checkh(selected_mixed_asc[14:15], concat_data[1:0]);
        `checkh(selected_whole_asc[14:15], concat_data[1:0]);
      end
    end

    concat_done = 1;
  end

  // Output streams must reorder drive enables and weak pulls along with data.
  logic [6:0] stream_enable;
  logic [6:0] stream_data;
  bit stream_done = 0;
  wire [6:0] stream_right;
  wire [6:0] stream_left;
  wire [6:0] stream_pairs;
  wire [6:0] stream_nested;
  wire [6:0] stream_unaligned;
  wire [6:0] stream_right_observed;
  wire [6:0] stream_left_observed;
  wire [6:0] stream_pairs_observed;
  wire [6:0] stream_nested_observed;
  wire [6:0] stream_unaligned_observed;
  stream_pull_mod right_stream (
      .enable(stream_enable), .data(stream_data), .pad({>>{stream_right}}),
      .observed(stream_right_observed)
  );
  stream_pull_mod left_stream (
      .enable(stream_enable), .data(stream_data), .pad({<<{stream_left}}),
      .observed(stream_left_observed)
  );
  stream_pull_mod pair_stream (
      .enable(stream_enable), .data(stream_data), .pad({<<2{stream_pairs}}),
      .observed(stream_pairs_observed)
  );
  stream_pull_mod nested_stream (
      .enable(stream_enable), .data(stream_data),
      .pad({<<2{{>>{stream_nested[6:4]}}, {<<{stream_nested[3:0]}}}}),
      .observed(stream_nested_observed)
  );
  // Both nested streams have a short slice, including on the readback path.
  stream_pull_mod unaligned_stream (
      .enable(stream_enable), .data(stream_data), .pad({<<3{{<<2{stream_unaligned}}}}),
      .observed(stream_unaligned_observed)
  );
  initial begin
    logic [6:0] expected;
    logic [6:0] pair_expected;
    logic [6:0] triple_expected;
    for (int cyc = 0; cyc < 16; ++cyc) begin
      stream_enable = 7'(cyc * 23);
      stream_data = 7'(cyc * 19);
      expected = (stream_data & stream_enable) | (7'h25 & ~stream_enable);
      pair_expected = {expected[1:0], expected[3:2], expected[5:4], expected[6]};
      triple_expected = {expected[2:0], expected[5:3], expected[6]};
      #1;
      `checkh(stream_right, expected);
      `checkh(stream_left, {expected[0], expected[1], expected[2], expected[3],
                            expected[4], expected[5], expected[6]});
      `checkh(stream_pairs, pair_expected);
      `checkh(stream_nested, {pair_expected[6:4], pair_expected[0], pair_expected[1],
                              pair_expected[2], pair_expected[3]});
      `checkh(stream_unaligned, {triple_expected[1:0], triple_expected[3:2],
                                 triple_expected[5:4], triple_expected[6]});
      `checkh(stream_right_observed, expected);
      `checkh(stream_left_observed, expected);
      `checkh(stream_pairs_observed, expected);
      `checkh(stream_nested_observed, expected);
      `checkh(stream_unaligned_observed, expected);
    end
    stream_done = 1;
  end

  // Wide streams must remain vector operations, including non-word-aligned slices.
  localparam int WIDE_WIDTH = 4095;
  logic wide_enable;
  logic wide_external_enable;
  logic [WIDE_WIDTH-1:0] wide_data;
  wire [WIDE_WIDTH-1:0] wide_reverse;
  wire [WIDE_WIDTH-1:0] wide_blocks;
  wire [WIDE_WIDTH-1:0] wide_reverse_observed;
  wire [WIDE_WIDTH-1:0] wide_blocks_observed;
  bit wide_stream_done = 0;
  wide_stream_pull_mod wide_bit_stream (
      .enable(wide_enable), .data(wide_data), .pad({<<{wide_reverse}}),
      .observed(wide_reverse_observed)
  );
  wide_stream_pull_mod wide_block_stream (
      .enable(wide_enable), .data(wide_data), .pad({<<33{wide_blocks}}),
      .observed(wide_blocks_observed)
  );
  assign wide_reverse = wide_external_enable ? wide_data : 'z;
  assign wide_blocks = wide_external_enable ? wide_data : 'z;
  initial begin
    logic [WIDE_WIDTH-1:0] reverse_expected;
    logic [WIDE_WIDTH-1:0] blocks_expected;
    logic [WIDE_WIDTH-1:0] blocks_readback;
    for (int cyc = 0; cyc < 16; ++cyc) begin
      wide_enable = cyc % 3 == 1;
      wide_external_enable = cyc % 3 == 2;
      wide_data = WIDE_WIDTH'({128{32'(cyc * 19 + 7)}});
      for (int i = 0; i < WIDE_WIDTH; ++i) begin
        reverse_expected[WIDE_WIDTH-1-i] = wide_data[i];
      end
      for (int start = 0; start < WIDE_WIDTH; start += 33) begin
        int bits;
        bits = start + 33 <= WIDE_WIDTH ? 33 : WIDE_WIDTH - start;
        for (int i = 0; i < 33 && start + i < WIDE_WIDTH; ++i) begin
          blocks_expected[WIDE_WIDTH-start-bits+i] = wide_data[start+i];
          blocks_readback[start+i] = wide_data[WIDE_WIDTH-start-bits+i];
        end
      end
      #1;
      if (wide_enable) begin
        `checkh(wide_reverse, reverse_expected);
        `checkh(wide_blocks, blocks_expected);
        `checkh(wide_reverse_observed, wide_data);
        `checkh(wide_blocks_observed, wide_data);
      end else if (wide_external_enable) begin
        `checkh(wide_reverse, wide_data);
        `checkh(wide_blocks, wide_data);
        `checkh(wide_reverse_observed, reverse_expected);
        `checkh(wide_blocks_observed, blocks_readback);
      end else begin
        `checkh(wide_reverse[WIDE_WIDTH-1], 1'b1);
        `checkh(wide_reverse[1:0], 2'b10);
        `checkh(wide_reverse[WIDE_WIDTH-2:2] === 'z, 1'b1);
        `checkh(wide_blocks[WIDE_WIDTH-33], 1'b1);
        `checkh(wide_blocks[2:1], 2'b01);
        `checkh(wide_blocks[WIDE_WIDTH-1:WIDE_WIDTH-32] === 'z, 1'b1);
        `checkh(wide_blocks[WIDE_WIDTH-34:3] === 'z, 1'b1);
        `checkh(wide_blocks[0] === 1'bz, 1'b1);
        `checkh(wide_reverse_observed[0], 1'b1);
        `checkh(wide_reverse_observed[WIDE_WIDTH-1:WIDE_WIDTH-2], 2'b01);
        `checkh(wide_blocks_observed[0], 1'b1);
        `checkh(wide_blocks_observed[WIDE_WIDTH-1:WIDE_WIDTH-2], 2'b01);
      end
    end
    wide_stream_done = 1;
  end
endmodule

`default_nettype wire
