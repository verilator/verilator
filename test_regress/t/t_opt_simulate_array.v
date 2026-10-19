// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

function integer fun;
  integer array[0:0];
  begin
    array[0] = 10;
    fun = array[0];
  end
endfunction

// Writes then reads each element of a large array, one by one
function automatic int sumElements(int n);
  int array[16000];
  int sum = 0;
  for (int i = 0; i < n; ++i) array[i] = i;
  for (int i = 0; i < n; ++i) sum += array[i];
  return sum;
endfunction

module test ();
  begin
    localparam something = fun();
    localparam int SUM = sumElements(16000);
    initial begin
      `checkd(something, 10);
      `checkd(SUM, 16000 * 15999 / 2);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
