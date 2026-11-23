// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define STRINGIFY(x) `"x`"
// verilog_format: on

module t;

  reg [175:0] hex[15:0];

  integer i;
  integer fd;
  string filename;

  initial begin
    // No warning as has addresses
    $readmemh("t/t_sys_readmem_bad_end2.mem", hex, 0, 15);
    // Warning as wrong end address
    $readmemh("t/t_sys_readmem_bad_end.mem", hex, 0, 15);

    filename = {`STRINGIFY(`TEST_OBJ_DIR), "/dat.mem"};
    fd = $fopen(filename, "w");
    $fdisplay(fd, "11 22 33");
    $fclose(fd);

    // Warning as file has more data words than the range, and loading stops at finish
    foreach (hex[i]) hex[i] = 'hff;
    $readmemh(filename, hex, 1, 2);
    `checkh(hex[0], 'hff);
    `checkh(hex[1], 'h11);
    `checkh(hex[2], 'h22);
    `checkh(hex[3], 'hff);
    `checkh(hex[4], 'hff);
    `checkh(hex[15], 'hff);
    // Same when descending
    foreach (hex[i]) hex[i] = 'hff;
    $readmemh(filename, hex, 6, 5);
    `checkh(hex[0], 'hff);
    `checkh(hex[3], 'hff);
    `checkh(hex[4], 'hff);
    `checkh(hex[5], 'h22);
    `checkh(hex[6], 'h11);
    `checkh(hex[7], 'hff);
    `checkh(hex[8], 'hff);
    `checkh(hex[15], 'hff);

    // Warning as address in file is outside the range, and loading stops
    fd = $fopen(filename, "w");
    $fdisplay(fd, "11");
    $fdisplay(fd, "@5");
    $fdisplay(fd, "22");
    $fclose(fd);
    foreach (hex[i]) hex[i] = 'hff;
    $readmemh(filename, hex, 1, 2);
    `checkh(hex[0], 'hff);
    `checkh(hex[1], 'h11);
    `checkh(hex[2], 'hff);
    `checkh(hex[4], 'hff);
    `checkh(hex[5], 'hff);
    `checkh(hex[6], 'hff);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
