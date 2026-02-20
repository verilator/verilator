// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;

  function int f1(output int o1);
    fork begin
      #1 $stop;
      f1 = 0;
      o1 = 0;
    end join_none
  endfunction

  function int f2(inout io2);
    fork begin
      f2 = #5 0; $stop;
      io2 = 0;
    end join_none
  endfunction

  event e;
  function int f3(output int o3);
    fork begin
      @e $stop;
      f3 = 0;
      o3 = 0;
    end join_none
  endfunction

  function int f4(inout int io4);
    fork begin
      f4 = @e 0; $stop;
      io4 = 0;
    end join_none
  endfunction

  int i;

  function int f5(output int o5);
    fork begin
      wait(i == 0) $stop;
      f5 = 0;
      o5 = 0;
    end join_none
  endfunction

endmodule
