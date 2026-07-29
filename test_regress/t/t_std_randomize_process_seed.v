// DESCRIPTION: Verilator: std::randomize follows process RNG seeding
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t;
  typedef bit [94:0] wide_t;

  task automatic sample_after_process_seed(input int seed, output int scalar_values[4],
                                           output wide_t wide_values[4]);
    process p;
    p = process::self();
    p.srandom(seed);
    foreach (scalar_values[i]) begin
      `checkd(std::randomize(scalar_values[i]), 1);
      `checkd(std::randomize(wide_values[i]), 1);
    end
  endtask

`ifdef TEST_CONSTRAINT_SOLVER
  task automatic sample_with_after_process_seed(input int seed, output int values[4]);
    process p;
    p = process::self();
    p.srandom(seed);
    foreach (values[i]) begin
      `checkd(std::randomize(values[i]) with {values[i] inside {[32'h1000_0000 : 32'h7fff_ffff]};},
              1);
    end
  endtask
`endif

  initial begin
    int scalar_first[4];
    int scalar_second[4];
    wide_t wide_first[4];
    wide_t wide_second[4];
`ifdef TEST_CONSTRAINT_SOLVER
    int constrained_first[4];
    int constrained_second[4];
`endif

    sample_after_process_seed(32'h1357_2468, scalar_first, wide_first);
    sample_after_process_seed(32'h1357_2468, scalar_second, wide_second);

    foreach (scalar_first[i]) begin
      `checkd(scalar_second[i], scalar_first[i]);
      `checkh(wide_second[i], wide_first[i]);
    end

`ifdef TEST_CONSTRAINT_SOLVER
    sample_with_after_process_seed(32'h1357_2468, constrained_first);
    sample_with_after_process_seed(32'h1357_2468, constrained_second);

    foreach (constrained_first[i]) `checkd(constrained_second[i], constrained_first[i]);
`endif

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
