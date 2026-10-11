// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2017 Todd Strader
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef struct packed {
    logic [31 : 0] a;
    logic [31 : 0] b;
  } params_t;

  typedef struct {
    int a;
    int b;
  } uparams_t;

  typedef struct {
    int a;
    int q[$];
  } queue_t;

  localparam params_t P = '{a: 5, b: 1};
  localparam P6 = f_add(P);
  localparam P14 = f_add2(2, 3, f_add(P));
  localparam P24 = f_add2(7, 8, 9);
  localparam U15 = f_uadd('{a: 7, b: 8});
  localparam Q1 = f_queue(1);

  initial begin
    // Should never get here
    $write("*-* All Finished *-*\n");
    $finish;
  end

  function integer f_add(input params_t params);
    f_add = params.a + params.b;
    if (f_add == 15) $fatal(2, "f_add = 15");
  endfunction

  // Speced ok: function called from function
  function integer f_add2(input [31:0] a, input [31:0] b, input [31:0] c);
    params_t params;
    params = '{a: a, b: b};
    f_add2 = f_add(params) + c;
  endfunction

  // Unpacked structure argument, shown in the message
  function integer f_uadd(input uparams_t params);
    f_uadd = params.a + params.b;
    if (f_uadd == 15) $fatal(2, "f_uadd = 15");
  endfunction

  // Structure with a member that a constant function can't hold
  function integer f_queue(input int a);
    queue_t s;
    s.a = a;
    f_queue = s.a;
  endfunction
endmodule
