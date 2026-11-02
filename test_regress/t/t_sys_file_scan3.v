// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface myif;
  logic [10:0] a;
  logic [255:0] b;
endinterface

module t;
  typedef struct packed {
    logic [10:0] a;
    logic [2:0] b;
  } test_struct_t;

  typedef struct packed {
    logic [1023:0] x;
    logic [1023:0] y;
  } wide_struct_t;

  typedef struct {
    int b;
  } unpacked_t;

  myif m();

  initial begin
    integer file_handle;
    integer scan;
    test_struct_t test;
    logic [13:0] test2;
    wide_struct_t wide;
    logic [255:0] wideps;
    unpacked_t up;
    logic [10:0] addr;
    string s;
    file_handle = $fopen("t/t_sys_file_scan3.dat", "r");
    // Non-addressable destinations: a packed member and a part-select
    scan = $fscanf(file_handle, "%h", test.a);
    `checkd(scan, 1);
    `checkd(test.a, 291);  // 11'h123
    `checkd(test.b, 0);
    scan = $fscanf(file_handle, "%h", test2[10:3]);
    `checkd(scan, 1);
    `checkd(test2, 528);  // 8'h42 at bits [10:3]
    // Wide non-addressable destinations
    scan = $fscanf(file_handle, "%h", wide.x);
    `checkd(scan, 1);
    `checkd(wide.x, 291);  // 11'h123
    `checkd(wide.y, 0);
    scan = $fscanf(file_handle, "%h", wideps[100:3]);
    `checkd(scan, 1);
    `checkd(wideps[100:3], 66);  // 8'h42 at bits [100:3]
    // Interface members (narrow and wide)
    scan = $fscanf(file_handle, "%h", m.a);
    `checkd(scan, 1);
    `checkd(m.a, 291);  // 11'h123
    scan = $fscanf(file_handle, "%h", m.b);
    `checkd(scan, 1);
    `checkd(m.b, 66);  // 8'h42
    // Unpacked struct member: addressable, so no rewrite happens
    scan = $fscanf(file_handle, "%d", up.b);
    `checkd(scan, 1);
    `checkd(up.b, 42);
    // $sscanf into a packed member
    s = "6";
    scan = $sscanf(s, "%d", test.b);
    `checkd(scan, 1);
    `checkd(test.b, 6);
    // Mixed addressable and non-addressable destinations
    scan = $fscanf(file_handle, "%h%h", addr, test2[10:3]);
    `checkd(scan, 2);
    `checkd(addr, 291);  // 11'h123
    `checkd(test2, 528);  // 8'h42 at bits [10:3]

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
