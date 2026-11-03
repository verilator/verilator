// DESCRIPTION: Verilator: Test hierarchical references through interface modports
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface data_if;
  logic [7:0] data;
  logic [7:0] generate_data;
  logic [7:0] mod_data;
  logic [7:0] mod_data_arr[2];
  logic [7:0] task_data;
  enum logic [7:0] {ENUM_VALUE = 8'h77} enum_storage;

  function automatic logic [7:0] add_one(input logic [7:0] value);
    return value + 1'b1;
  endfunction

  task automatic set_task_data(input logic [7:0] value);
    task_data = value;
  endtask

  modport output_modport(
      output generate_data, mod_data, mod_data_arr, task_data,
      import add_one, set_task_data
  );
endinterface

module modport_writer (
    data_if.output_modport bus,
    input logic [7:0] value
);
  assign bus.mod_data_arr[0] = value;
endmodule

module modport_forward (
    data_if.output_modport bus,
    input logic [7:0] value
);
  modport_writer writer (
      bus,
      value
  );
endmodule

module t;
  data_if array_if[2] ();
  data_if matrix_if[2][2] ();

  modport_writer writer (
      array_if[0].output_modport,
      8'h55
  );
  modport_forward forwarder (
      array_if[1].output_modport,
      8'h5a
  );

  assign array_if[0].data = 8'h11;
  assign array_if[1].data = 8'h22;
  assign array_if[0].output_modport.mod_data = 8'h33;
  assign array_if[1].output_modport.mod_data = 8'h44;
  assign array_if[1].output_modport.mod_data_arr[1] = 8'h66;
  assign matrix_if[1][0].output_modport.mod_data = 8'h88;

  for (genvar i = 0; i < 2; ++i) begin : g_array
    assign array_if[i].output_modport.generate_data = 8'(8'h70 + i);
  end

  logic [7:0] function_result;
  assign function_result = array_if[0].output_modport.add_one(8'h68);

  logic [7:0] enum_value = array_if[1].output_modport.ENUM_VALUE;

  initial begin
    array_if[1].output_modport.set_task_data(8'h69);
    #0;
    `checkh(array_if[0].data, 8'h11);
    `checkh(array_if[1].data, 8'h22);
    `checkh(array_if[0].output_modport.mod_data, 8'h33);
    `checkh(array_if[1].output_modport.mod_data, 8'h44);
    `checkh(array_if[0].output_modport.mod_data_arr[0], 8'h55);
    `checkh(array_if[1].output_modport.mod_data_arr[0], 8'h5a);
    `checkh(array_if[1].output_modport.mod_data_arr[1], 8'h66);
    `checkh(array_if[0].output_modport.generate_data, 8'h70);
    `checkh(array_if[1].output_modport.generate_data, 8'h71);
    `checkh(array_if[1].output_modport.task_data, 8'h69);
    `checkh(matrix_if[1][0].output_modport.mod_data, 8'h88);
    `checkh(function_result, 8'h69);
    `checkh(enum_value, 8'h77);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
