// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
  integer infile;

  typedef struct packed {
    logic [10:0] a;
    logic [2:0]  b;
  } test_struct_t;

  test_struct_t test;
  integer d;

  initial begin
    string s;
    integer n;
    infile = $fopen("t/t_sys_fscanf_partselect.dat", "r");
    // A packed struct member and a part-select have no address, so the
    // results of the calls are written back to the destinations
    n = $fscanf(infile, "%d", test.a);
    if (n != 1) $stop;
    if (test.a != 11'd255) $stop;
    n = $fscanf(infile, "%d", d[3:0]);
    if (n != 1) $stop;
    if (d[3:0] != 4'd15) $stop;
    s = "6";
    n = $sscanf(s, "%d", test.b);
    if (n != 1) $stop;
    if (test.b != 3'd6) $stop;
    $fclose(infile);
    $write("*-* All Finished *-*\n");
    $finish(0);  // Test arguments to finish
  end

endmodule
