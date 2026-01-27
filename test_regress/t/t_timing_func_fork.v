// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;

  function int f1;
    fork begin
      #1 $stop;
    end join_none
    f1 = 0;
  endfunction

  function int f2;
    fork begin
      int x;
      x = #5 0; $stop;
    end join_none
    f2 = 0;
  endfunction

  event e;
  function int f3;
    fork begin
      int x;
      @e $stop;
      x = 0;
    end join_none
    f3 = 0;
  endfunction

  function int f4;
    fork begin
      int x;
      x = @e 0; $stop;
    end join_none
    f4 = 0;
  endfunction

  int i;

  function int f5;
    fork begin
      int x;
      wait(i == 0) $stop;
      x = 0;
    end join_none
    f5 = 0;
  endfunction

  initial begin
    fork begin
      i = f1();
      $write("*-* All Finished *-*\n");
      $finish;
    end join_none
  end

endmodule
