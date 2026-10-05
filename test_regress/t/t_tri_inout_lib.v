// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`ifdef LIB_CREATE
module secret (
    input clk,
    input [67:3] en,
    input [67:3] data,
    inout wire [67:3] pad,
    inout wire [2:8] reverse_pad,
    inout wire [6:0] receive_pad,
    output wire [67:3] q,
    output wire [2:8] reverse_q,
    output wire [6:0] receive_q,
    output logic [67:3] sampled
);
  for (genvar i = 3; i <= 67; ++i) begin
    assign pad[i] = en[i] ? data[i] : 1'bz;
  end
  for (genvar i = 2; i <= 8; ++i) begin
    assign reverse_pad[i] = en[i+1] ? data[i+1] : 1'bz;
  end
  assign q = pad;
  assign reverse_q = reverse_pad;
  assign receive_q = receive_pad;
  always @(posedge clk) sampled <= pad;
endmodule
`else
module t (
    input clk
);
  int cyc = 0;
  wire [67:3] en = 65'h15555555555555555 ^ {65{cyc[0]}} ^ (65'(cyc) << 31);
  wire [67:3] data = 65'h123456789abcdef01 ^ 65'(cyc) ^ (65'(cyc) << 59);
  wire [67:3] external_data = ~data;
  wire [67:3] expected = (en & data) | (~en & external_data);
  wire [67:3] pad;
  wire [2:8] reverse_pad;
  wire [6:0] receive_pad = data[9:3];
  wire [67:3] q;
  wire [2:8] reverse_q;
  wire [6:0] receive_q;
  wire [67:3] sampled;
  logic [67:3] expected_sampled;

`ifdef LIB_SPLIT
  wire [67:3] pad__out;
  wire [67:3] pad__en;
  wire [2:8] reverse_pad__out;
  wire [2:8] reverse_pad__en;
  wire [6:0] receive_pad__out;
  wire [6:0] receive_pad__en;
`endif

  secret dut (
      .clk(clk),
      .en(en),
      .data(data),
      .pad(pad),
      .reverse_pad(reverse_pad),
      .receive_pad(receive_pad),
      .q(q),
      .reverse_q(reverse_q),
      .receive_q(receive_q),
`ifdef LIB_SPLIT
      .pad__out(pad__out),
      .pad__en(pad__en),
      .reverse_pad__out(reverse_pad__out),
      .reverse_pad__en(reverse_pad__en),
      .receive_pad__out(receive_pad__out),
      .receive_pad__en(receive_pad__en),
`endif
      .sampled(sampled)
  );

  for (genvar i = 3; i <= 67; ++i) begin
    assign pad[i] = en[i] ? 1'bz : external_data[i];
`ifdef LIB_SPLIT
    assign pad[i] = pad__en[i] ? pad__out[i] : 1'bz;
`endif
  end
  for (genvar i = 2; i <= 8; ++i) begin
    assign reverse_pad[i] = en[i+1] ? 1'bz : external_data[i+1];
`ifdef LIB_SPLIT
    assign reverse_pad[i] = reverse_pad__en[i] ? reverse_pad__out[i] : 1'bz;
`endif
    always @(negedge clk) `checkh(reverse_q[i], expected[i+1]);
  end

  always @(posedge clk) begin
    expected_sampled <= expected;
    cyc <= cyc + 1;
  end
  always @(negedge clk) begin
    `checkh(q, expected);
    `checkh(receive_q, data[9:3]);
`ifdef LIB_SPLIT
    `checkh(receive_pad__out, 7'b0);
    `checkh(receive_pad__en, 7'b0);
`endif
    `checkh(sampled, expected_sampled);
    if (cyc == 64) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
`endif
