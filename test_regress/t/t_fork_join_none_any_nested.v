// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

event evt1, evt2, evt3;

class Foo;
  task do_something(int cap1, int cap2);
    fork
      begin
        $display("outer fork: %d", cap1);
        fork
          $display("inner fork: %d", cap2);
          ->evt2;
          fork
            $display("innermost fork: %d", cap2);
            ->evt3;
          join_none
        join_none
      end
      ->evt1;
    join_any
  endtask
endclass

module t();
  reg a, b, c;

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
  always @(evt3) begin
    c <= 1;
  end

  always @(a, b, c) begin
    if (a & b & c) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
