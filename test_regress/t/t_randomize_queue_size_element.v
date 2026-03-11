// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, cond) \
begin \
  automatic longint prev_result; \
  automatic int ok; \
  if (!bit'(cl.randomize())) $stop; \
  prev_result = longint'(field); \
  if (!(cond)) $stop; \
  repeat(20) begin \
    longint result; \
    if (!bit'(cl.randomize())) $stop; \
    result = longint'(field); \
    if (!(cond)) $stop; \
    if (result != prev_result) ok = 1; \
    prev_result = result; \
  end \
  if (ok != 1) $stop; \
end

class SizeElemQ;
  rand int q[$];
  constraint c {
    q.size() > 1;
    q.size() < 6;
    q[0] > 100;
    q[1] == q[0] + 1;
  }
endclass

class SizeElemQ2;
  rand int q[$];
  rand int min_sz;
  constraint c {
    min_sz inside {[2:4]};
    q.size() == min_sz;
    foreach (q[i]) q[i] inside {[10:20]};
    q[0] != q[q.size() - 1];
  }
endclass

class SizeElemDynArr;
  rand int da[];
  constraint c {
    da.size() inside {[3:5]};
    da[0] < 50;
    da[da.size() - 1] > 50;
    foreach (da[i]) da[i] inside {[1:100]};
  }
endclass

module t;
  initial begin
    automatic SizeElemQ obj = new;
    automatic SizeElemQ2 obj2 = new;
    automatic SizeElemDynArr obj3 = new;

    `check_rand(obj, obj.q[0],
                obj.q.size() > 1 && obj.q.size() < 6
                && obj.q[0] > 100
                && obj.q[1] == obj.q[0] + 1);

    `check_rand(obj2, obj2.q[0],
                obj2.min_sz inside {[2:4]}
                && obj2.q.size() == obj2.min_sz
                && obj2.q[0] inside {[10:20]}
                && obj2.q[obj2.q.size() - 1] inside {[10:20]}
                && obj2.q[0] != obj2.q[obj2.q.size() - 1]);

    `check_rand(obj3, obj3.da[0],
                obj3.da.size() inside {[3:5]}
                && obj3.da[0] < 50
                && obj3.da[obj3.da.size() - 1] > 50);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
