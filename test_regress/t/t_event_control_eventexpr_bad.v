// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  Foo other;
  Foo other_array[10];
  event evt;
  event evt_array[10];

  function automatic event get_event();
    return evt;
  endfunction

  task send_events();
    ->evt; // Should be good
    ->get_event(); // Should fail - it's not a hierarchical identifier
    ->other.evt; // Should be good
    for (int i = 0; i < 10; i++) begin
      ->evt_array[i]; // Should fail - it's an expression that's not a
                      // hierarhical identifier, because of the variable
                      // used for indexing
    end
    // Should be good because we are using constant selectors
    ->evt_array[2];
    ->other.evt_array[1];
    ->other_array[3].evt;
    ->other_array[0].evt_array[7];
  endtask
endclass
