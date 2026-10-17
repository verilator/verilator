// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2014 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;
  reg [63:0] crc;
  reg [63:0] sum;

  parameter NPAD = 4;

  tri pad[NPAD-1:0];  // Array
  wire [NPAD-1:0] data0 = crc[0+:4];
  wire [NPAD-1:0] data1 = crc[8+:4];
  wire [NPAD-1:0] en = crc[16+:4];

  for (genvar g = 0; g < NPAD; ++g) begin : gpad
    Pad pad1 (
        .pad(pad[g]),
        .ena(en[g]),
        .data(data1[g])
    );
    Pad pad0 (
        .pad(pad[g]),
        .ena(!en[g]),
        .data(data0[g])
    );
  end

  // Each constant-index driver should resolve only its own element, even on a large array.
  wire [6:0] large_pad [3:129];
  for (genvar i = 3; i <= 129; ++i) begin
    wire enable = crc[i % 64];
    wire [6:0] value = 7'(crc >> (i % 57)) ^ 7'(i);
    assign large_pad[i] = enable ? value : 7'bz;
    assign large_pad[i] = enable ? 7'bz : ~value;
    always @(negedge clk) begin
      if (cyc > 1) `checkh(large_pad[i], enable ? value : ~value);
    end
  end

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= {60'h0, pad[3], pad[2], pad[1], pad[0]} ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
    if (cyc == 0) begin
      // Setup
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= 64'h0;
    end
    else if (cyc < 10) begin
      sum <= 64'h0;
    end
    else if (cyc < 90) begin
    end
    else if (cyc == 99) begin
      $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
      if (crc !== 64'hc77bb9b3784ea091) $stop;
      // What checksum will we end up with (above print should match)
      `define EXPECTED_SUM 64'he09fe6f2dfd7a302
      if (sum !== `EXPECTED_SUM) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Pad (
    inout pad,
    input ena,
    input data
);
  assign pad = ena ? data : 1'bz;
endmodule
