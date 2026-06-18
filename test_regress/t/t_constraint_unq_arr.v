// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Based on t_constraint_unsup_unq_arr.v
// We only check uniqueness for small # of elements on a large range
// as Z3 does not actually give unique elements (bug?) as of Jul 2026.

module t;
  class UniqueMultipleArray;
    rand bit [15:0] arr[4];
    rand bit [15:0] darr[];
    rand bit [15:0] queue[$];
    rand bit [15:0] queue_c[$:3];
    rand bit [15:0] assoc[int];

    constraint c {
      unique {arr};
      unique {darr};
      unique {queue};
      unique {queue_c};
      unique {assoc};
    }

    function new;
      darr = new[4];
      queue = {0, 0, 0, 0};
      queue_c = {0, 0, 0, 0};
      assoc = '{0: 0, 1: 0, 3: 0, 5: 0};
    endfunction

    function bit check_unique();
      // static array
      for (int i = 0; i < $size(arr); i++) begin
        for (int j = i + 1; j < $size(arr); j++) begin
          if (arr[i] == arr[j]) begin
            $error("UNIQUENESS VIOLATION: arr[%0d] == arr[%0d] == 0x%h", i, j, arr[i]);
            return 0;
          end
        end
      end
      // dynamic array
      for (int i = 0; i < darr.size(); i++) begin
        for (int j = i + 1; j < darr.size(); j++) begin
          if (darr[i] == darr[j]) begin
            $error("UNIQUENESS VIOLATION: darr[%0d] == darr[%0d] == 0x%h", i, j,
                  darr[i]);
            return 0;
          end
        end
      end
      // queue
      for (int i = 0; i < queue.size(); i++) begin
        for (int j = i + 1; j < queue.size(); j++) begin
          if (queue[i] == queue[j]) begin
            $error("UNIQUENESS VIOLATION: queue[%0d] == queue[%0d] == 0x%h", i, j,
                  queue[i]);
            return 0;
          end
        end
      end
      // queue_c
      for (int i = 0; i < queue_c.size(); i++) begin
        for (int j = i + 1; j < queue_c.size(); j++) begin
          if (queue_c[i] == queue_c[j]) begin
            $error("UNIQUENESS VIOLATION: queue_c[%0d] == queue_c[%0d] == 0x%h", i, j,
                  queue_c[i]);
            return 0;
          end
        end
      end
      // assoc array
      foreach (assoc[i]) begin
        foreach (assoc[j]) begin
          if (i == j) begin
            continue;
          end
          if (assoc[i] == assoc[j]) begin
            $error("UNIQUENESS VIOLATION: assoc[%0d] == assoc[%0d] == 0x%h", i, j,
                  assoc[i]);
            return 0;
          end
        end
      end
      return 1;
    endfunction

endclass : UniqueMultipleArray

  initial begin
    automatic UniqueMultipleArray a = new();
    a.randomize();
    assert(a.check_unique());

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule : t
