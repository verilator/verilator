// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

static int counts[10];

class Foo;
  static task do_something();
    for (int i = 0; i < 10; i++)
      frk : fork
        int ii = i;
        #(10 + i) begin
          $display("i: %d, ii: %d", i, ii);
          if (counts[ii]++ != 0)
            $stop;
        end
      join_none : frk
  endtask
endclass

module t();
  initial begin
    int desired_counts[10] = '{10{1}};
    counts = '{10{0}};

    Foo::do_something();
    #20;

    if (counts != desired_counts)
      $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
