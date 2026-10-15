// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  import "DPI-C" context function void vpi_deposit(input string path, input int value);
  import "DPI-C" context function void vpi_force(input string path, input int value);

  logic [7:0] driver /* verilator public_flat_rw */ /* verilator forceable */ = 8'h0f;
  logic [7:0] driven /* verilator public_flat_rw */ /* verilator forceable */;
  logic [7:0] another = 8'haa;

  assign driven = driver;

  always #20 driver = another;

  initial begin
    #15 driver = 8'hff;
  end

  initial begin
    #5;
    `checkh(driven, 8'h0f);

    #5
    vpi_deposit("t.driven", 32'ha5);
    `checkh(driven, 8'ha5);

    // IEEE 1800-2023 38.34: [A deposited net value] shall remain in effect
    // until one of the drivers of the net changes value.
    #4;
    `checkh(driven, 8'ha5);

    // `driven` is updated when `driver` changes.
    #2;
    `checkh(driven, 8'hff);

    // `driven` is updated when `driver` takes `another` value.
    #5;
    `checkh(driven, 8'haa);

    // `driven` changes it's value to match `driver` forced value
    #5;
    vpi_force("t.driver", 32'hbe);
    #0;
    `checkh(driven, 8'hbe);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
