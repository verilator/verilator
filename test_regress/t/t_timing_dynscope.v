// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns / 1ns

static int counts[10];

class Foo;
  static task do_something();
    for (int i = 0; i < 10; i++) begin // Should create a dynamic scope for `i`
      int ci = i; // Should create another dynamic scope for `ci`, local to the begin block
      fork begin
        #10;
        $display("ci: %d, i: %d", ci, i);
        if (i != 10)
          $stop;
        if (counts[ci-1]++ > 0)
          $stop;
      end join_none
      ci++;
    end
  endtask
endclass

module t();
  initial begin
    int desired_counts[10];
    counts = '{10{0}};
    desired_counts = '{10{1}};

    Foo::do_something();
    #20;
    if (counts != desired_counts)
      $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
