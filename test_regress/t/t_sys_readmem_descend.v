// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`define STRINGIFY(x) `"x`"

module t;
  logic [7:0] mem[0:7];
  logic [7:0] assoc[int];
  logic [7:0] got[0:7];
  int fd;
  string filename;
  initial begin
    filename = {`STRINGIFY(`TEST_OBJ_DIR), "/mem1.hex"};
    fd = $fopen(filename, "w");
    $fdisplay(fd, "11");
    $fdisplay(fd, "22");
    $fdisplay(fd, "33");
    $fclose(fd);

    // Start above finish loads with decrementing addresses, IEEE 1800-2023 21.4
    foreach (mem[i]) mem[i] = 8'hff;
    $readmemh(filename, mem, 5, 3);
    `checkh({mem[2], mem[3], mem[4], mem[5], mem[6]}, 40'hff_33_22_11_ff);

    // Ascending still increments
    foreach (mem[i]) mem[i] = 8'hff;
    $readmemh(filename, mem, 3, 5);
    `checkh({mem[2], mem[3], mem[4], mem[5], mem[6]}, 40'hff_11_22_33_ff);

    // $writemem with start above finish writes decrementing addresses
    filename = {`STRINGIFY(`TEST_OBJ_DIR), "/mem2.hex"};
    foreach (mem[i]) mem[i] = 8'(8'h10 + i);
    $writememh(filename, mem, 5, 3);
    foreach (got[i]) got[i] = 8'hff;
    $readmemh(filename, got, 0, 2);
    `checkh({got[0], got[1], got[2], got[3]}, 32'h15_14_13_ff);

    // Ascending still increments
    filename = {`STRINGIFY(`TEST_OBJ_DIR), "/mem3.hex"};
    $writememh(filename, mem, 3, 5);
    foreach (got[i]) got[i] = 8'hff;
    $readmemh(filename, got, 0, 2);
    `checkh({got[0], got[1], got[2], got[3]}, 32'h13_14_15_ff);

    // Associative arrays
    assoc[2] = 8'h22;
    assoc[4] = 8'h44;
    assoc[6] = 8'h66;
    filename = {`STRINGIFY(`TEST_OBJ_DIR), "/mem4.hex"};
    $writememh(filename, assoc, 5, 2);
    foreach (got[i]) got[i] = 8'hff;
    $readmemh(filename, got);
    `checkh({got[2], got[3], got[4], got[6]}, 32'h22_ff_44_ff);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
