// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0


class Foo;
  event evt1;
  task automatic assign_new();
    event evt2;
    evt1 = evt2;
  endtask
endclass
