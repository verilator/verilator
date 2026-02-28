// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

`define DELAY 10

class Foo;
  task wait_dynamically();
    #`DELAY;
  endtask

  static task wait_statically();
    #`DELAY;
  endtask
endclass

module t;
  Foo foo = new;

  initial begin
    foo.wait_dynamically();
    if ($time != `DELAY) $stop;
    Foo::wait_statically();
    if ($time != 2*`DELAY) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
