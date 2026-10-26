// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(g,e) do if ((g) !== (e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
`define STRINGIFY(x) `"x`"
// verilog_format: on

module t;
  typedef bit [6:0] memory_t[4:2];
  typedef bit [64:0] wide_memory_t[2:4];
  memory_t mem  /* verilator forceable */;
  wide_memory_t wide_mem  /* verilator forceable */;
  memory_t expected;
  wide_memory_t wide_expected;
  memory_t readback;
  wide_memory_t wide_readback;
  string hex_file = {`STRINGIFY(`TEST_OBJ_DIR), "/memory.hex"};
  string bin_file = {`STRINGIFY(`TEST_OBJ_DIR), "/memory.bin"};

  task check_dump;
    $writememh(hex_file, mem);
    $readmemh(hex_file, readback);
    foreach (readback[i]) `checkh(readback[i], expected[i]);
    $writememb(bin_file, mem);
    $readmemb(bin_file, readback);
    foreach (readback[i]) `checkh(readback[i], expected[i]);

    $writememh(hex_file, wide_mem);
    $readmemh(hex_file, wide_readback);
    foreach (wide_readback[i]) `checkh(wide_readback[i], wide_expected[i]);
    $writememb(bin_file, wide_mem);
    $readmemb(bin_file, wide_readback);
    foreach (wide_readback[i]) `checkh(wide_readback[i], wide_expected[i]);

    readback = '{default: '1};
    $writememh(hex_file, mem, 3, 3);
    $readmemh(hex_file, readback, 3, 3);
    `checkh(readback[3], expected[3]);
    `checkh(readback[2], 7'h7f);
    `checkh(readback[4], 7'h7f);

    $writememh(hex_file, expected);
    $readmemh(hex_file, readback);
    foreach (readback[i]) `checkh(readback[i], expected[i]);
  endtask

  initial begin
    for (int cycle = 0; cycle < 4; ++cycle) begin
      foreach (expected[i]) expected[i] = 7'(cycle * 13 + i);
      foreach (wide_expected[i]) begin
        wide_expected[i] = 65'h1_1234_5678_9abc_def0 ^ 65'(cycle * 7 + i);
      end
      mem = expected;
      wide_mem = wide_expected;
      #1;
      check_dump();

      force mem[3] = 7'h65;
      force wide_mem[3] = 65'h1_fedc_ba98_7654_3210;
      expected[3] = 7'h65;
      wide_expected[3] = 65'h1_fedc_ba98_7654_3210;
      check_dump();

      release mem[3];
      release wide_mem[3];
      check_dump();
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
