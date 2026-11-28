// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef int arr_t[3];
typedef bit [30:0] w_t;
typedef w_t row_t[5:3];

class Cls;
  int cnt;
  int init_depth;
  function arr_t get_arr(int depth);
    arr_t arr = (depth > 1) ? get_arr(depth - 1) : '{init_depth, init_depth * 2, init_depth * 3};
    cnt++;
    return arr;
  endfunction
endclass

module t;
  Cls c = new;
  row_t rq[$];
  function automatic row_t take();
    return rq.pop_front();
  endfunction
  initial begin
    arr_t arr;
    c.init_depth = 5;
    arr = (c.init_depth > 0) ? c.get_arr(5) : '{1, 2, 3};

    if (arr[0] != 5) $stop;
    if (arr[1] != 10) $stop;
    if (arr[2] != 15) $stop;

    if (c.cnt != 5) $stop;

    begin
      // A source or target with a new value each evaluation is evaluated once, not per element
      arr_t q[$];
      arr_t aa[int];
      arr_t rows[4];
      int pos;
      q = '{'{1, 2, 3}, '{4, 5, 6}};
      arr = q.pop_front();
      `checkd(arr[0], 1);
      `checkd(arr[2], 3);
      `checkd(q.size(), 1);
      begin
        // Also into a slice or a queue, and with the opposite range direction
        int row[4];
        int rev[2:0];
        int dq[$];
        q.push_back('{7, 8, 9});
        q.push_back('{10, 11, 12});
        row[1:3] = q.pop_front();
        `checkd(row[1], 4);
        `checkd(row[3], 6);
        `checkd(q.size(), 2);
        rev = q.pop_front();
        `checkd(rev[2], 7);
        `checkd(rev[0], 9);
        `checkd(q.size(), 1);
        dq = q.pop_front();
        `checkd(dq[0], 10);
        `checkd(dq.size(), 3);
        `checkd(q.size(), 0);
      end
      aa[7] = arr;
      `checkd(aa[7][1], 2);
      foreach (rows[i, j]) rows[i][j] = 10 * i + j;
      for (int seed = 1; seed <= 20; seed++) begin
        void'($urandom(seed));
        arr = rows[2'($urandom())];
        void'($urandom(seed));
        pos = 32'(2'($urandom()));
        `checkd(arr[0], rows[pos][0]);
        `checkd(arr[2], rows[pos][2]);
      end
    end
    begin
      // A target element of an associative array or queue, which a write may create
      int aa[int][2];
      int q[$][2];
      int d[][2];
      int src[2];
      aa[3] = '{1, 2};
      q.push_back('{0, 0});
      q[0] = '{3, 4};
      q[1] = '{5, 6};
      `checkh(aa[3][0], 1);
      `checkh(aa[3][1], 2);
      `checkh(q.size(), 2);
      `checkh(q[0][1], 4);
      `checkh(q[1][0], 5);
      src = '{7, 8};
      aa[4] = src;
      q[0] = src;
      d = new[1];
      d[0] = src;
      `checkh(aa[4][1], 8);
      `checkh(q[0][0], 7);
      `checkh(d[0][1], 8);
    end
    begin
      // A row popped by a function, or popped into a whole row
      row_t r;
      row_t a;
      row_t got;
      r = '{31'h1, 31'h2, 31'h4};
      repeat (3) rq.push_back(r);
      got = take();
      `checkh(rq.size(), 2);
      `checkh(got[4], 31'h2);
      a = rq.pop_front();
      `checkh(rq.size(), 1);
      `checkh(a[3], 31'h4);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
