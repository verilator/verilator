// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// Test: Inline foreach constraints on dynamic arrays and queues of class objects

class Inner;
  rand bit [7:0] val;
  rand bit [3:0] tag;

  function new();
    val = 0;
    tag = 0;
  endfunction
endclass

class OuterDyn;
  rand Inner items[];

  function new(int size = 3);
    items = new[size];
    foreach (items[i]) items[i] = new();
  endfunction
endclass

class OuterQueue;
  rand Inner items[$];

  function new(int size = 3);
    Inner tmp;
    for (int i = 0; i < size; i++) begin
      tmp = new();
      items.push_back(tmp);
    end
  endfunction
endclass

module t;
  OuterDyn od;
  OuterDyn od_arr[5];
  OuterQueue oq;

  initial begin
    // === Test 1: Dynamic array with inline foreach constraint ===
    od = new(3);

    if (od.randomize() with {
          foreach (items[i]) {
            items[i].val > 10;
            items[i].val < 200;
            items[i].tag > 0;
          }
        } == 0) begin
      $display("FAIL: dyn randomize() returned 0");
      $stop;
    end

    foreach (od.items[i]) begin
      if (!(od.items[i].val > 10 && od.items[i].val < 200)) begin
        $display("FAIL: dyn items[%0d].val=%0d out of range", i, od.items[i].val);
        $stop;
      end
      if (od.items[i].tag == 0) begin
        $display("FAIL: dyn items[%0d].tag=%0d should be > 0", i, od.items[i].tag);
        $stop;
      end
    end

    // === Test 2: Empty dynamic array (should succeed trivially) ===
    od = new(0);

    if (od.randomize() with {
          foreach (items[i]) {
            items[i].val > 10;
          }
        } == 0) begin
      $display("FAIL: empty dyn randomize() returned 0");
      $stop;
    end

    // === Test 3: Queue with inline foreach constraint ===
    oq = new(3);

    if (oq.randomize() with {
          foreach (items[i]) {
            items[i].val > 50;
            items[i].val < 150;
            items[i].tag > 0;
          }
        } == 0) begin
      $display("FAIL: queue randomize() returned 0");
      $stop;
    end

    foreach (oq.items[i]) begin
      if (!(oq.items[i].val > 50 && oq.items[i].val < 150)) begin
        $display("FAIL: queue items[%0d].val=%0d out of range", i, oq.items[i].val);
        $stop;
      end
      if (oq.items[i].tag == 0) begin
        $display("FAIL: queue items[%0d].tag=%0d should be > 0", i, oq.items[i].tag);
        $stop;
      end
    end

    // === Test 4: Array of objects with inline constraint for sub-object members ===
    // Verifies member resolution AND runtime enforcement when randomize()
    // target is array-indexed (regression test for verilator/verilator#7431)
    foreach (od_arr[i]) begin
      od_arr[i] = new(3);
      assert(od_arr[i].randomize() with {
        od_arr[i].items[0].val > 8'd10;
        od_arr[i].items[0].val < 8'd200;
        od_arr[i].items[0].tag > 0;
      } != 0);

      if (!(od_arr[i].items[0].val > 10 && od_arr[i].items[0].val < 200)) begin
        $display("FAIL: od_arr[%0d].items[0].val=%0d out of range",
                 i, od_arr[i].items[0].val);
        $stop;
      end
      if (od_arr[i].items[0].tag == 0) begin
        $display("FAIL: od_arr[%0d].items[0].tag=%0d should be > 0",
                 i, od_arr[i].items[0].tag);
        $stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
