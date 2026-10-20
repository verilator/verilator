// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A timed process whose statements are too large to split at the top level,
// as the call sites of a task are in the items of a case statement. Parts of
// the items are moved into separate functions, which must keep the local
// variables of the process, jumps and loop conditions working.

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int edges = 0;
  always @(posedge clk) edges <= edges + 1;

  task automatic step(input int v, inout int acc);
    for (int k = 0; k < 3; k++) begin
      @(posedge clk);
      if (v == 5 && k == 1) return;
      acc += v * k + 1;
    end
  endtask

  // A task that is not inlined is a coroutine of its own: the moved statements
  // use its arguments and local variables, which are passed by reference
  class Cls;
    int total;
    task run(input int n, const ref int lim, inout int acc);
      automatic int loc = 0;
      for (int i = 0; i < n; i++) begin
        automatic int inner = i * 2;
        if (i == 1) begin
          @(posedge clk);
          loc += inner;
          acc += loc + lim;
          if (acc > 1000) acc = 1000;
          loc = loc * 3 + 1;
          acc += loc % 7;
          @(posedge clk);
          acc += inner * lim;
        end
        else begin
          #1;
          acc += inner + n;
          loc += lim;
          if (loc > 50) loc -= 50;
          if (loc > 3) @(posedge clk);  // Declares a variable in a moved statement
          acc += loc * 2;
          #1;
          acc ^= i;
        end
      end
      total = acc;
    endtask
  endclass

  initial begin
    automatic int acc = 0;  // Live across the case items and loop iterations
    automatic int last = 0;
    automatic int c;
    for (c = 0; c < 12; c++) begin
      case (c)
        0: begin
          step(1, acc);
          last = acc;
        end
        1: begin
          step(2, acc);
          if (acc > 10) break;
        end
        2: begin
          #1;
          acc += 3;
        end
        3: step(4, acc);
        4: step(5, acc);
        5: begin
          for (int j = 0; j < 4; j++) begin
            if (j == 2) continue;
            acc += j;
          end
          step(6, acc);
        end
        6: begin
          step(7, acc);
          if (acc[0]) acc += 100;
          else acc += 200;
        end
        7: begin
          step(8, acc);
          step(9, acc);
        end
        default: begin
          step(c, acc);
          acc++;
        end
      endcase
    end
    `checkd(c, 1);
    `checkd(last, 6);
    `checkd(acc, 15);
    for (c = 2; c < 12; c++) begin
      case (c)
        2: begin
          #1;
          acc += 3;
        end
        3: step(4, acc);
        4: step(5, acc);
        5: begin
          for (int j = 0; j < 4; j++) begin
            if (j == 2) continue;
            acc += j;
          end
          step(6, acc);
        end
        6: begin
          step(7, acc);
          if (acc[0]) acc += 100;
          else acc += 200;
        end
        7: begin
          step(8, acc);
          step(9, acc);
        end
        default: begin
          step(c, acc);
          acc++;
        end
      endcase
    end
    `checkd(acc, 370);
    `checkd(edges, 34);
    // The largest movable statements are followed by a statement that cannot move
    for (c = 0; c < 4; c++) begin
      step(8, acc);
      step(9, acc);
      if (c == 2) break;
    end
    `checkd(c, 2);
    `checkd(acc, 541);
    begin
      automatic Cls cls = new;
      automatic int lim = 5;
      acc = 0;
      cls.run(4, lim, acc);
      `checkd(acc, 168);
      `checkd(cls.total, 168);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
