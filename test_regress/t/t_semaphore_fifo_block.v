// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns / 1ns
module t;
  semaphore sem = new(2);

  initial begin
    fork
      begin
        #1;
        sem.get(4);
        $write("[%0t] A got 4\n", $time);
        #1;
        sem.put(3);
        $write("[%0t] A put 3\n", $time);
      end
      begin
        #2;
        sem.get(3);
        $write("[%0t] B got 3\n", $time);
      end
      begin
        #3;
        sem.get(1);
        $write("[%0t] C got 1\n", $time);
        sem.put(1);
        $write("[%0t] C put 1\n", $time);
      end
      begin
        #4;
        sem.put(2);
        $write("[%0t] D put 2\n", $time);
      end
    join

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
