// DESCRIPTION: Verilator: Verilog Test module
//
// Based on code Copyright (C) 2019-2021  The SymbiFlow Authors.
// SPDX-License-Identifier: ISC

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
// verilog_format: on

module t;

  function int abort_break();
    int x;
    static int return_on = 1;
    randsequence( main )
      main : first second third;
      first : { x = x + 20; };
      second : { if (return_on == 1) return; x = x + 10; };
      third : { x = x + 5;};
    endsequence
    return x;
  endfunction


  initial begin
    int x;
    bit flag = 1;
    int switch = 1;
    int break_on = 1;
    static int return_on = 1;

    x = 0;
    randsequence(main)
      main : first second done;
      first : { x = x + 1; };
      second : { x = x + 2; };
      done : { x = x + 3; };
    endsequence
    `checkd(x, 6);

    x = 0;
    randsequence(main)
      main : or_first | or_second;
      or_first : { x += -2; };
      or_second : { x += 2; };
    endsequence
    if (x != 2 && x != -2) $stop;

    x = 0;
    randsequence(main)
      main : or_first := 1 | or_second := 0;
      or_first : { x += 2; };
      or_second : { x += -2; };
    endsequence
    `checkd(x, 2);

    x = 0;
    flag = 1;
    randsequence(main)
      main : first;
      first : { if (flag) x = 10; else x = 5; };
    endsequence
    `checkd(x, 10);

    x = 0;
    flag = 0;
    randsequence(main)
      main : first;
      first : { if (flag) x = 10; else x = 5; };
    endsequence
    `checkd(x, 5);

    x = 0;
    flag = 1;
    randsequence(main)
      main : first;
      first : if (flag) second else third;
      second : { x = 10; };
      third : { x = 5; };
    endsequence
    `checkd(x, 10);

    x = 0;
    switch = 1;
    randsequence(main)
      main : case (switch)
        0 : zero;
        1 : first;
        2 : second;
        default : third;
      endcase;
      zero : { x = 0; };
      first : { x = 10; };
      second : { x = 2; };
      third : { x = 3; };
    endsequence
    `checkd(x, 10);

    x = 0;
    randsequence(main)
      main : first;
      first : repeat(10) second;
      second : { x = x + 1; };
    endsequence
    `checkd(x, 10);

    x = 0;
    randsequence(main)
      main : rand join first second;
      first : { x = x + 20; };
      second : { x = x - 10; };
    endsequence
    `checkd(x, 10);

    x = 0;
    randsequence(main)
      main : rand join (0.5) first second;
      first : { x = x + 20; };
      second : { x = x - 10; };
    endsequence
    `checkd(x, 10);

    x = 0;
    break_on = 1;
    randsequence(main)
      main : first second third;
      first : { x = x + 10; };
      second : { if (break_on == 1) break; } fourth;
      third : { x = x + 10; };
      fourth : { x = x + 15; };
    endsequence
    `checkd(x, 10);

    x = 0;
    break_on = 0;
    randsequence(main)
      main : first second third;
      first : { x = x + 10; };
      second : { if (break_on == 1) break; } fourth;
      third : { x = x + 10; };
      fourth : { x = x + 15; };
    endsequence
    `checkd(x, 35);

    x = 0;
    return_on = 1;
    randsequence(main)
      main : first second third;
      first : { x = x + 20; };
      second : { if (return_on == 1) return; x = x + 10; };
      third : { x = x + 5; };
    endsequence
    `checkd(x, 25);

    x = 0;
    return_on = 0;
    randsequence(main)
      main : first second third;
      first : { x = x + 20; };
      second : { if (return_on == 1) return; x = x + 10; };
      third : { x = x + 5; };
    endsequence
    `checkd(x, 35);

`ifndef VERILATOR  // Unsupported randsequence functions
    x = 0;
    randsequence(main)
      main : first second third;
      first : add(10);
      second : add(5);
      third : add(2);
      void add(int y) : { x = x + y; };
      void add(int y) : sub_a sub_b;  // This is presumably legal, try it
    endsequence
    `checkd(x, 17);
`endif

    x = abort_break();
    `checkd(x, 25);

    $finish;
  end

endmodule
