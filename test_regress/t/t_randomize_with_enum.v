// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkinrange(gotv,minv,maxv) do if (((minv) > (gotv)) || ((maxv) < (gotv))) begin $write("%%Error: %s:%0d: got=%0d min=%0d max=%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

typedef enum bit[3:0] {
  ONE,
  TWO,
  THREE,
  FOUR,
  FIVE
} enum_t;

class withConstraint;
  rand enum_t e;

  constraint c{
    e != ONE;
  };
endclass

class withoutConstraint;
  rand enum_t e;
  rand enum_t f;
endclass

module t;
  withConstraint wc;
  withoutConstraint woc;

  initial begin
    int rand_result;
    wc = new;
    woc = new;

    repeat (20) begin
      rand_result = wc.randomize();
      `checkd(rand_result, 1);
      `checkinrange(int'(wc.e), int'(TWO), int'(FIVE));

      rand_result = woc.randomize();
      `checkd(rand_result, 1);
      `checkinrange(int'(woc.e), int'(ONE), int'(FIVE));

      rand_result = (wc.randomize() with {
        e != TWO;
      });
      `checkd(rand_result, 1);
      `checkinrange(int'(wc.e), int'(THREE), int'(FIVE));

      rand_result = (woc.randomize() with {
        e != ONE;
      });
      `checkd(rand_result, 1);
      `checkinrange(int'(woc.e), int'(TWO), int'(FIVE));
      `checkinrange(int'(woc.f), int'(ONE), int'(FIVE));

      rand_result = (woc.randomize() with {
        e != ONE;
        f != ONE;
      });
      `checkd(rand_result, 1);
      `checkinrange(int'(woc.e), int'(TWO), int'(FIVE));
      `checkinrange(int'(woc.f), int'(TWO), int'(FIVE));
    end

    $write("*-* all finished *-*\n");
    $finish;
  end
endmodule
