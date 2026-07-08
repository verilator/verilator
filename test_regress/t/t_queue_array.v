// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  int normal_queue[$];
  int array_of_queues[3][$];
  int aa_of_queues[int][$];

  function void test_normal_queue();
    $display("[%0t] %m: Testing single queue (int normal_queue [$])", $realtime);
    `checkd(normal_queue.size(), 0);
    repeat (4) normal_queue.push_back($urandom);
    `checkd(normal_queue.size(), 4);
    repeat (4) void'(normal_queue.pop_front());
    `checkd(normal_queue.size(), 0);
  endfunction

  function void test_array_of_queues();
    $display("[%0t] %m: Testing array of queues (int array_of_queues [3][$])", $realtime);
    array_of_queues[0] = {};
    array_of_queues[1] = {};
    array_of_queues[2] = {};

    for (int i = 0; i < 3; i++) begin
      `checkd(array_of_queues[i].size(), 0);
    end

    for (int i = 0; i < 3; i++) begin
      for (int j = 0; j < 4; j++) begin : push_4_items
        array_of_queues[i].push_back($urandom);
        $display("[%0t] %m: array_of_queues, pushed item to queue %0d: [0]=%p [1]=%p [2]=%p",
                 $realtime, i, array_of_queues[0], array_of_queues[1], array_of_queues[2]);
        `checkd(array_of_queues[i].size(), j + 1);
      end
    end

    for (int i = 0; i < 3; i++) begin : pop_4_items_from_each
      repeat (4) void'(array_of_queues[i].pop_front());
      `checkd(array_of_queues[i].size(), 0);
    end
  endfunction

  function void test_aa_of_queues();
    $display("[%0t] %m: Testing associative-array of queues (int aa_of_queues [int][$])",
             $realtime);

    aa_of_queues[0] = {};
    aa_of_queues[1] = {};
    aa_of_queues[2] = {};

    for (int i = 0; i < 3; i++) begin
      `checkd(aa_of_queues[i].size(), 0);
    end

    for (int i = 0; i < 3; i++) begin
      for (int j = 0; j < 4; j++) begin : push_4_items
        aa_of_queues[i].push_back($urandom);
        $display("[%0t] %m: aa_of_queues, pushed item to queue %0d: [0]=%p [1]=%p [2]=%p",
                 $realtime, i, aa_of_queues[0], aa_of_queues[1], aa_of_queues[2]);
        `checkd(aa_of_queues[i].size(), j + 1);
      end
    end

    for (int i = 0; i < 3; i++) begin
      repeat (4) void'(aa_of_queues[i].pop_front());
      `checkd(aa_of_queues[i].size(), 0);
    end
  endfunction


  initial begin
    test_normal_queue();
    test_aa_of_queues();
    test_array_of_queues();
    $finish;
  end

endmodule
