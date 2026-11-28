// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;

  function int f1;
    fork
      begin
        #1 $stop;
      end
    join_none
    f1 = 0;
  endfunction

  function int f2;
    fork
      begin
        int x;
        x = #5 0;
        $stop;
      end
    join_none
    f2 = 0;
  endfunction

  event e;
  function int f3;
    fork
      begin
        int x;
        @e $stop;
        x = 0;
      end
    join_none
    f3 = 0;
  endfunction

  function int f4;
    fork
      begin
        int x;
        x = @e 0;
        $stop;
      end
    join_none
    f4 = 0;
  endfunction

  int i;

  function int f5;
    fork
      begin
        int x;
        wait (i == 0) $stop;
        x = 0;
      end
    join_none
    f5 = 0;
  endfunction

  // A function forking a process with a delay, called from an array method 'with'. This
  // covers timing inside a 'with', which works without special handling as well.
  int q[$] = '{1, 2};
  int s;
  function automatic int f6(int v);
    fork
      begin
        #1 s = v;
      end
    join_none
    return v;
  endfunction

  initial s = q.sum() with (f6(item));

  initial begin
    fork
      begin
        i = f1();
        $write("*-* All Finished *-*\n");
        $finish;
      end
    join_none
  end

endmodule
