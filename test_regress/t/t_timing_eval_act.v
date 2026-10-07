// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 1;
  logic clk_inv;
  event a;
  event e;

  // This $c is required to prevent inlining clk_inv as ~clk
  assign clk_inv = $c(1) & ~clk;

  // This is needed to provide right order of resumption in scheduler
  initial begin
    @a;
    @(posedge clk_inv);
    @e;
  end

  initial begin
    forever begin
      @(posedge clk_inv) begin
        clk = 1;
        ->e;
        @e;
      end
    end
  end
  initial begin
    @a;
    @e;
    if (clk_inv != 0) $stop;
    $finish;
  end
  initial begin
    #1;
    ->a;
    clk = 0;
    #2 $stop;
  end

  // Trigger debug text must show a long name as written, not the hashed name (Issue #8747)
  `define lc clock_signal_name_that_is_well_over_the_limit_where_verilator_hashes_identifiers_to_keep_generated_cpp_names_and_file_names_short
  logic `lc = 0;
  initial begin
    #10 `lc = 1;
    @(posedge `lc);
  end
endmodule
