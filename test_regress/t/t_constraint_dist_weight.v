// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

class DistScalar;
  rand bit [7:0] x;
  constraint c { x dist { 8'd0 := 1, 8'd255 := 3 }; }
endclass

class DistRange;
  rand bit [7:0] x;
  constraint c { x dist { [8'd0:8'd9] :/ 1, [8'd10:8'd19] :/ 3 }; }
endclass

class DistZeroWeight;
  rand bit [7:0] x;
  constraint c { x dist { 8'd0 := 0, 8'd1 := 1, 8'd2 := 1 }; }
endclass

class DistAllZeroWeight;
  rand bit [7:0] x;
  constraint c { x dist { 8'd0 := 0, 8'd1 := 0, 8'd2 := 0 }; }
endclass

class DistVarWeight;
  rand bit [7:0] x;
  int w1, w2;
  constraint c { x dist { 8'd0 := w1, 8'd255 := w2 }; }
endclass

class DistVarWeightRange;
  rand bit [7:0] x;
  int w1, w2;
  constraint c { x dist { [8'd0:8'd9] :/ w1, [8'd10:8'd19] :/ w2 }; }
endclass

module t;
  initial begin
    DistScalar sc;
    DistRange rg;
    DistZeroWeight zw;
    DistAllZeroWeight azw;
    DistVarWeight vw;
    DistVarWeightRange vwr;
    int count_high;
    int count_range_high;
    int total;

    total = 2000;

    // := scalar weights: expect ~75% for value 255
    sc = new;
    count_high = 0;
    repeat (total) begin
      `checkd(sc.randomize(), 1);
      if (sc.x == 8'd255) count_high++;
      else `checkd(sc.x, 0);
    end
    `check_range(count_high, total * 60 / 100, total * 90 / 100);

    // :/ range weights: expect ~75% in [10:19]
    rg = new;
    count_range_high = 0;
    repeat (total) begin
      `checkd(rg.randomize(), 1);
      if (rg.x >= 8'd10 && rg.x <= 8'd19) count_range_high++;
      else if (rg.x > 8'd9) begin
        $write("%%Error: x=%0d outside valid range [0:19]\n", rg.x);
        `stop;
      end
    end
    `check_range(count_range_high, total * 60 / 100, total * 90 / 100);

    // Zero weight: value 0 must never appear
    zw = new;
    repeat (total) begin
      `checkd(zw.randomize(), 1);
      if (zw.x == 8'd0) begin
        $write("%%Error: zero-weight value 0 was selected\n");
        `stop;
      end
      `check_range(zw.x, 1, 2);
    end

    // All-zero weights: dist constraint is effectively unconstrained, randomize succeeds
    azw = new;
    repeat (20) begin
      `checkd(azw.randomize(), 1);
    end

    // Variable := scalar weights: w1=1, w2=3 => expect ~75% for value 255
    vw = new;
    vw.w1 = 1;
    vw.w2 = 3;
    count_high = 0;
    repeat (total) begin
      `checkd(vw.randomize(), 1);
      if (vw.x == 8'd255) count_high++;
      else `checkd(vw.x, 0);
    end
    `check_range(count_high, total * 60 / 100, total * 90 / 100);

    // Variable :/ range weights: w1=1, w2=3 => expect ~75% in [10:19]
    vwr = new;
    vwr.w1 = 1;
    vwr.w2 = 3;
    count_range_high = 0;
    repeat (total) begin
      `checkd(vwr.randomize(), 1);
      if (vwr.x >= 8'd10 && vwr.x <= 8'd19) count_range_high++;
      else if (vwr.x > 8'd9) begin
        $write("%%Error: x=%0d outside valid range [0:19]\n", vwr.x);
        `stop;
      end
    end
    `check_range(count_range_high, total * 60 / 100, total * 90 / 100);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
