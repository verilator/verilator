// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  // Test: a change to any element wakes an event control on an unpacked array
  logic [6:0] arr[3:1] = '{7'd1, 7'd2, 7'd3};
  int arr_wakes = 0;
  always @(arr) ++arr_wakes;

  initial begin
    #1 arr[1] = 7'd9;
    #1 `checkd(arr_wakes, 1);
    arr[3] = 7'd8;
    #1 `checkd(arr_wakes, 2);
  end

  // Test: a change to any member wakes an event control on an unpacked structure
  typedef struct {
    int a;
    logic [14:0] b;
  } st_t;
  st_t st = '{a: 5, b: 15'h7};
  int st_wakes = 0;
  always @(st) ++st_wakes;

  initial begin
    #1 st.b = 15'h1234;
    #1 `checkd(st_wakes, 1);
    st.a = 6;
    #1 `checkd(st_wakes, 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
