// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  event evt;
  function automatic event get_event();
    return evt;
  endfunction
  task send_event();
    ->get_event();
  endtask
endclass
