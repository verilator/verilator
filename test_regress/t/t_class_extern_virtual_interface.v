// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface Bus #(
    parameter int WIDTH = 1
);
  logic [WIDTH-1:0] value;

  modport Source(output value);
endinterface

typedef virtual Bus #(7).Source SourceBus;

class Driver;
  extern function void drive_external(virtual Bus bus, logic value);
  extern function void drive_parameter(virtual Bus #(7) bus, logic [6:0] value);
  extern function void drive_modport(virtual Bus #(7).Source bus, logic [6:0] value);
  extern function void drive_array(virtual Bus #(7).Source buses[2], logic [6:0] value);
  extern function void drive_queue(virtual Bus #(7).Source buses[$], logic [6:0] value);
  extern function void drive_dyn(virtual Bus #(7).Source buses[], logic [6:0] value);
  extern function void drive_assoc(virtual Bus #(7).Source buses[int], logic [6:0] value);
  extern function SourceBus get_bus(SourceBus bus);

  function void drive_inline(virtual Bus bus, logic value);
    bus.value = value;
  endfunction
endclass

function void Driver::drive_external(virtual Bus bus, logic value);
  bus.value = value;
endfunction

function void Driver::drive_parameter(virtual Bus #(7) bus, logic [6:0] value);
  bus.value = value;
endfunction

function void Driver::drive_modport(virtual Bus #(7).Source bus, logic [6:0] value);
  bus.value = value;
endfunction

function void Driver::drive_array(virtual Bus #(7).Source buses[2], logic [6:0] value);
  buses[1].value = value;
endfunction

function void Driver::drive_queue(virtual Bus #(7).Source buses[$], logic [6:0] value);
  buses[1].value = value;
endfunction

function void Driver::drive_dyn(virtual Bus #(7).Source buses[], logic [6:0] value);
  buses[1].value = value;
endfunction

function void Driver::drive_assoc(virtual Bus #(7).Source buses[int], logic [6:0] value);
  buses[7].value = value;
endfunction

function SourceBus Driver::get_bus(SourceBus bus);
  return bus;
endfunction

module t;
  Bus bus();
  Bus #(7) parameter_bus();
  Bus #(7) bus_array[2]();
  Driver driver = new;

  initial begin
    automatic SourceBus returned_bus;
    automatic virtual Bus #(7).Source queue_buses[$];
    automatic virtual Bus #(7).Source dyn_buses[];
    automatic virtual Bus #(7).Source assoc_buses[int];

    bus.value = 1'b0;
    driver.drive_inline(bus, 1'b1);
    `checkd(bus.value, 1)

    driver.drive_external(bus, 1'b0);
    `checkd(bus.value, 0)

    driver.drive_parameter(parameter_bus, 7'd31);
    `checkd(parameter_bus.value, 31)

    driver.drive_modport(parameter_bus.Source, 7'd47);
    `checkd(parameter_bus.value, 47)

    driver.drive_array(bus_array, 7'd63);
    `checkd(bus_array[1].value, 63)

    queue_buses.push_back(parameter_bus.Source);
    queue_buses.push_back(bus_array[0].Source);
    driver.drive_queue(queue_buses, 7'd15);
    `checkd(bus_array[0].value, 15)

    dyn_buses = new[2];
    dyn_buses[0] = parameter_bus.Source;
    dyn_buses[1] = bus_array[1].Source;
    driver.drive_dyn(dyn_buses, 7'd23);
    `checkd(bus_array[1].value, 23)

    assoc_buses[7] = parameter_bus.Source;
    driver.drive_assoc(assoc_buses, 7'd39);
    `checkd(parameter_bus.value, 39)

    returned_bus = driver.get_bus(parameter_bus.Source);
    returned_bus.value = 7'd79;
    `checkd(parameter_bus.value, 79)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
