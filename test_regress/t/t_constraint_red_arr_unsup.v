// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class ReductionDynSubArr;
  rand int arr[5][];
  rand int a;

  typedef struct {
    rand int arr[];
  } Subcls;

  rand Subcls sc;

  function new();
    sc.arr = new[5];
    foreach (arr[i]) begin
      arr[i] = new [5];
    end
  endfunction

  constraint red_a {
    a + arr[0].sum() == 10;
    a + arr[1].product() == 10;
    a + arr[2].xor() == 10;
    a + arr[3].or() == 10;
    a + arr[4].and() == 10;
  }

  constraint red_b {
    a + sc.arr.sum() == 10;
    a + sc.arr.product() == 10;
    a + sc.arr.xor() == 10;
    a + sc.arr.or() == 10;
    a + sc.arr.and() == 10;
  }
endclass : ReductionDynSubArr

module t;
  initial begin
    automatic ReductionDynSubArr sub = new();
    void'(sub.randomize());
  end
endmodule : t
