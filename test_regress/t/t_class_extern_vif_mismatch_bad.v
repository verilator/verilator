// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface Bus #(
    parameter int WIDTH = 1
);
  logic [WIDTH-1:0] value;

  modport Source(output value);
  modport Sink(input value);
endinterface

interface OtherBus;
  logic value;
endinterface

class Driver;
  extern function void drive_modport_bad(virtual Bus.Source bus);  // <--- Error (modport)
  extern function void drive_iface_bad(virtual Bus bus);  // <--- Error (interface)
  extern function void drive_param_bad(virtual Bus #(7) bus);  // <--- Error (parameter)
  extern function void drive_queue_bad(virtual Bus.Source buses[$]);  // <--- Error (modport)
  extern function void drive_dyn_bad(virtual Bus buses[]);  // <--- Error (interface)
  extern function void drive_assoc_bad(virtual Bus #(7).Source buses[int]);  // <--- Error (parameter)
  extern function virtual Bus.Source get_bus_bad();  // <--- Error (return modport)
endclass

function void Driver::drive_modport_bad(virtual Bus.Sink bus);
endfunction

function void Driver::drive_iface_bad(virtual OtherBus bus);
endfunction

function void Driver::drive_param_bad(virtual Bus #(8) bus);
endfunction

function void Driver::drive_queue_bad(virtual Bus.Sink buses[$]);
endfunction

function void Driver::drive_dyn_bad(virtual OtherBus buses[]);
endfunction

function void Driver::drive_assoc_bad(virtual Bus #(8).Source buses[int]);
endfunction

function virtual Bus.Sink Driver::get_bus_bad();
endfunction

module t;
endmodule
