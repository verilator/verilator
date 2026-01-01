// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// The number of clocks in the clock vector

localparam int N = 5;

`ifdef LIB_CREATE
// This is built with --lib-create

module sub (
    input logic [N-1:0] clkvec,
    output logic [7:0] cnt[N]
);

  for (genvar i = 0; i < N; ++i) begin : GEN
    logic [7:0] counter = 8'd0;
    always @(posedge clkvec[i]) counter <= counter + 8'd1;
    assign cnt[i] = counter;
  end

endmodule

`else
// This is built as the top level

module top;

  logic [N-1:0] clkvec = N'(0);
  logic [7:0] cnt[N];

  // Generate clocks by rotation
  always #5 clkvec = {clkvec[N-2:0], clkvec[N-1] | ~|clkvec};

  sub sub_i (
      clkvec,
      cnt
  );

  always @(clkvec) begin
    #1;
    $write("%10t %05b", $time, clkvec);
    for (int i = N - 1; i >= 0; --i) begin
      $write(" cnt[%0d]=%02d", i, cnt[i]);
    end
    $write("\n");

    // No counter should reach above 10
    for (int i = 0; i < N; ++i) begin
      if (cnt[i] > 10) $stop;
    end

    // Conclude when all counters reach 10
    begin
      static bit done = 1'b1;
      for (int i = 0; i < N; ++i) begin
        if (cnt[i] != 10) done = 1'b0;
      end
      if (done) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
  end

endmodule

`endif
