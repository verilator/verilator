// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int cnt;

  function automatic int count(int v);
    ++cnt;
    return v;
  endfunction

  // Items are evaluated in order, each at most once, until the first match
  function automatic int pick(int x);
    case (x)
      count(1): return 10;
      count(2), count(3): return 20;
      default: return 30;
    endcase
  endfunction

  class Cls;
    int m;
    function new(int m);
      this.m = m;
    endfunction
  endclass

  typedef struct {int m;} s_t;

  initial begin
    int hit;
    cnt = 0;
    `checkd(pick(1), 10);
    `checkd(cnt, 1);
    cnt = 0;
    `checkd(pick(2), 20);
    `checkd(cnt, 2);
    cnt = 0;
    `checkd(pick(3), 20);
    `checkd(cnt, 3);
    cnt = 0;
    `checkd(pick(4), 30);
    `checkd(cnt, 3);
    // The case expression is evaluated once
    cnt = 0;
    case (count(2))
      count(1): hit = 1;
      count(2): hit = 2;
      default: hit = 3;
    endcase
    `checkd(hit, 2);
    `checkd(cnt, 3);
    // A member select of an impure case expression is also evaluated once
    begin
      Cls cq[$];
      s_t sq[$];
      Cls c;
      c = new(2);
      cq.push_back(c);
      c = new(5);
      cq.push_back(c);
      case (cq.pop_front().m)
        1: hit = 1;
        2: hit = 2;
        default: hit = 3;
      endcase
      `checkd(hit, 2);
      `checkd(cq.size(), 1);
      sq.push_back('{m: 2});
      sq.push_back('{m: 5});
      case (sq.pop_front().m)
        1: hit = 1;
        2: hit = 2;
        default: hit = 3;
      endcase
      `checkd(hit, 2);
      `checkd(sq.size(), 1);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
