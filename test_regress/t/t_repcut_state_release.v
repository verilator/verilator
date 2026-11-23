// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk, clk2, reset, enable,
    input logic [14:0] data,
    output logic [14:0] a
`ifdef PUBLIC_STATE
        /* verilator public_flat_rw */
`endif
    ,
    output logic [14:0] b, c, snapshot, swap_a, swap_b, guarded, later, observed,
    output logic [6:0] narrow,
    output logic [94:0] wide
`ifdef DECODER_STATE
    , input logic [127:0] mask,
    output logic [127:0] decoded, decoded_live
`endif
);
`ifdef FOREIGN_IMPORT
  import "DPI-C" function int unsigned state_release_observe(input int unsigned value);
`endif
`ifdef DECODER_STATE
  // A state-dependent decoder must provide the old value to clocked readers
  // and the new value to combinational readers after the same edge settles.
  for (genvar i = 0; i < 128; ++i) begin
    assign decoded_live[i] = (narrow == 7'(i)) ^ mask[i];
  end
  always @(posedge clk) begin
    if (reset) decoded <= '0;
    else if (enable) decoded <= decoded_live;
  end
`endif
  always @(posedge clk) begin
    if (reset) begin
      a <= 15'd1;
      b <= 15'd2;
      c <= 15'd3;
      swap_a <= 15'd7;
      swap_b <= 15'd11;
      guarded <= 15'd13;
      narrow <= 7'd0;
      wide <= 95'd1;
    end
    else begin
      if (enable) begin
        a <= data;
        b <= a;
        c <= b;
        narrow <= data[6:0];
        wide <= {data, wide[94:15]};
      end
      swap_a <= swap_b;
      swap_b <= swap_a;
      if (a[0]) guarded <= data;
      else guarded <= guarded ^ data;
    end
    // These must see old values, including when preceding guarded writes fire.
    snapshot <= a ^ b ^ c;
    later <= a ^ guarded;
  end
`ifdef EXTRA_OBSERVER
  initial begin
    observed = 15'd0;
    repeat (40) begin
      @(posedge clk);
      observed <= a;
    end
  end
`elsif SECOND_CLOCK
  always @(posedge clk2) observed <= a;
`elsif COMB_OBSERVER
  always @(a) begin
    observed = a;
    if (a == 15'h11) $display("Combinational observer %0d", a);
  end
`elsif FOREIGN_OBSERVER
  assign observed = 15'(state_release_observe(32'(a)));
`elsif USER_TABLE
  // User-written cache-shaped logic must not inherit the compiler's proof.
  logic fake_table [0:127];
  logic [6:0] previous = '0;
  initial for (int i = 0; i < 128; ++i) fake_table[i] = 1'b0;
  always @(narrow) begin
    fake_table[previous] = 1'b0;
    fake_table[narrow] = 1'b1;
    previous = narrow;
  end
  assign observed = {14'b0, fake_table[0]};
`else
  assign observed = 15'd0;
`endif
endmodule
