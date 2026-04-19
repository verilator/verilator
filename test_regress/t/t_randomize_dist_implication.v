// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class DistScalar;
  rand bit [7:0] x;
  rand bit mode;
  rand bit [1:0] mode2;
  constraint force_cond { mode == 1'b0; mode2 == 2'b00; }
  constraint c {
    if (mode) {
      x dist { 8'd0 := 1, 8'd255 := 3 };
    } else {
      (mode2 == '0) -> x dist { 8'd0 := 3, 8'd255 := 1 };
    }
  }
endclass

class DistChain;
  rand bit [7:0] x;
  rand bit a;
  rand bit b;
  constraint force_ab { a == 1'b1; b == 1'b1; }
  constraint c {
    a -> b -> x dist { 8'd0 := 3, 8'd255 := 1 };
  }
endclass

class DistForeachImpl;
  rand bit [7:0] arr [4];
  rand bit enb;
  constraint force_enb { enb == 1'b1; }
  constraint c {
    foreach (arr[i]) {
      enb -> arr[i] dist { 8'd10 := 1, 8'd20 := 1, 8'd30 := 1 };
    }
  }
endclass

module t;
  DistScalar obj;
  DistChain ch;
  DistForeachImpl fa;

  initial begin
    int p;
    obj = new;
    ch = new;
    fa = new;

    repeat (20) begin
      p = obj.randomize();
      `checkd(p, 1);
      // Implication is forced to fire by force_cond; x must be a bucket value.
      `checkd(obj.mode, 1'b0);
      `checkd(obj.mode2, 2'b00);
      `checkd((obj.x == 8'd0) || (obj.x == 8'd255), 1'b1);

      p = ch.randomize();
      `checkd(p, 1);
      `checkd(ch.a, 1'b1);
      `checkd(ch.b, 1'b1);
      `checkd((ch.x == 8'd0) || (ch.x == 8'd255), 1'b1);

      p = fa.randomize();
      `checkd(p, 1);
      `checkd(fa.enb, 1'b1);
      foreach (fa.arr[i]) begin
        `checkd((fa.arr[i] == 8'd10) || (fa.arr[i] == 8'd20)
                || (fa.arr[i] == 8'd30), 1'b1);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
