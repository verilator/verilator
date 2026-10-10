// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package types_pkg;
  virtual class Helper #(
      parameter int W = 13,
      parameter int N = 3
  );
    typedef logic [W-1:0] word_t;
    typedef logic [$bits(word_t)-1:0][N-1:0] matrix_t;

    static function automatic matrix_t make_data();
      matrix_t result = '0;
      for (int i = 0; i < $bits(word_t); i++) result[i] = '1;
      return result;
    endfunction

    static function automatic matrix_t value(input matrix_t arg);
      localparam matrix_t DATA = make_data();
      return DATA ^ arg;
    endfunction

    static function automatic int size();
      return $bits(matrix_t);
    endfunction
  endclass
endpackage

package use_pkg;
  import types_pkg::Helper;
  // Both uses specialize the class, leaving its default template uninstantiated.
  localparam logic [34:0] SMALL = Helper#(7, 5)::value('0);
  localparam logic [33:0] LARGE = Helper#(17, 2)::value('0);
endpackage

module t;
  initial begin
    `checkh(use_pkg::SMALL, 35'h7ffffffff);
    `checkh(use_pkg::LARGE, 34'h3ffffffff);
    `checkd(types_pkg::Helper#(7, 5)::size(), 35);
    `checkd(types_pkg::Helper#(17, 2)::size(), 34);
    for (int i = 0; i < 8; i++) begin
      `checkh(types_pkg::Helper#(7, 5)::value(35'(i)), 35'h7ffffffff ^ 35'(i));
      `checkh(types_pkg::Helper#(17, 2)::value(34'(i)), 34'h3ffffffff ^ 34'(i));
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
