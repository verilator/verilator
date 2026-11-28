// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Martin Velay
// SPDX-License-Identifier: CC0-1.0

class Item;
  int value;
endclass

module t;
  task automatic produce(output Item h);
    #1;
    h = new;
  endtask

  initial begin
    automatic Item h;
    fork
      // Bad: the forked process can outlive h
      produce(h);
      #10;
    join_any
    $finish;
  end
endmodule
