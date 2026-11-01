// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Non-blocking event triggers shall not trigger automatic events, as they update the event like a
// non-blocking assignment (IEEE 1800-2023 6.21, 15.5.1), but may trigger class properties

class Cls;
  event e;
  static event s_e;
  task trig();
    ->>e;  // OK
  endtask
endclass

module t;
  Cls c = new;
  event me;

  task automatic tk();
    event ae;
    ->>ae;  // Error
  endtask

  initial begin
    ->>me;  // OK
    ->>c.e;  // OK
    ->>Cls::s_e;  // OK
    c.trig();
    tk();
  end
endmodule
