// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

event evt1;
event evt2;

task send_evt1();
  ->evt1;
endtask
task send_evt2();
  ->evt2;
endtask

class Foo;
  task do_something(int cap1, int cap2);
    fork
      begin
        $display("outer fork: %d", cap1);
        fork
          $display("inner fork: %d", cap2);
          send_evt2();
        join_none
      end
      send_evt1();
    join_none
  endtask
endclass

module t();
  reg a, b;

  initial begin
    Foo foo;

    a = 1'b0;
    b = 1'b0;
    foo = new;
    foo.do_something(1, 2);
  end

  always @(evt1) begin
    a <= 1;
  end
  always @(evt2) begin
    b <= 1;
  end

  always @(a, b) begin
    if (a & b) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
