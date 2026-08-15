// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  localparam CYCLES = 10;

  int cyc = 0;

  wire logic last = cyc == CYCLES - 1;

  // Reports and returns zero if any two of the samples are the same
  function automatic bit all_different(input int samples[CYCLES]);
    for (int i = 0; i < CYCLES; ++i) begin
      for (int j = i + 1; j < CYCLES; ++j) begin
        if (samples[i] === samples[j]) begin
          $write("%%Error: samples %0d and %0d are both %0d\n", i, j, samples[i]);
          return 1'b0;
        end
      end
    end
    return 1'b1;
  endfunction

  // A seed must be referred to by the call only for this test to be effective

  // 2 operand $dist_*
  int dist_bi_seed;
  int dist_bi_values[CYCLES];

  // 3 operand $dist_*
  int dist_tri_seed;
  int dist_tri_values[CYCLES];

  // $random
  int random_seed;
  int random_values[CYCLES];

  // $urandom - seed or this is input, not inout
  int urandom_seed = 32'h4567_89ab;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    // 2 operand $dist_*
    dist_bi_values[cyc] = $dist_exponential(dist_bi_seed, 1000000);
    if (last) begin
      `checkd(all_different(dist_bi_values), 1'b1);
    end

    // 3 operand $dist_*
    dist_tri_values[cyc] = $dist_normal(dist_tri_seed, 100, 1000000);
    if (last) begin
      `checkd(all_different(dist_tri_values), 1'b1);
    end

    // $random
    random_values[cyc] = $random(random_seed);
    if (last) begin
      `checkd(all_different(random_values), 1'b1);
    end

    // $urandom - seed must not change
    void'($urandom(urandom_seed));
    `checkd(urandom_seed, 32'h4567_89ab);

    if (last) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
