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
    // A random case expression is drawn once
    for (int seed = 1; seed <= 8; ++seed) begin
      int unsigned value;
      int unsigned after;
      void'($urandom(seed));
      value = $urandom() % 8;
      after = $urandom();
      void'($urandom(seed));
      case ($urandom() % 8) inside
        [0 : 2]: hit = 1;
        [3 : 5]: hit = 2;
        default: hit = 3;
      endcase
      `checkd(hit, value <= 2 ? 1 : value <= 5 ? 2 : 3);
      value = $urandom();
      `checkd(value, after);
      // Also under unique and unique0, whose checks compare it with each item
      void'($urandom(seed));
      unique case (2'($urandom()))
        0, 1: hit = 1;
        2, 3: hit = 2;
      endcase
      void'($urandom(seed));
      unique0 case (2'($urandom()))
        0: hit = 3;
        1, 2, 3: hit = 4;
      endcase
      value = $urandom();
      `checkd(value, after);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
