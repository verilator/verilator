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
  logic [7:0] mod_data;
  logic [7:0] mod_data_arr[2];
  modport output_modport(output mod_data, output mod_data_arr);
endinterface

module modport_writer (
    data_if.output_modport bus,
    input logic [7:0] value
);
  assign bus.mod_data_arr[0] = value;
endmodule

module t;
  data_if array_if[2] ();
  modport_writer writer (
      array_if[0].output_modport,
      8'h55
  );

  assign array_if[0].data = 8'h11;
  assign array_if[1].data = 8'h22;
  assign array_if[0].output_modport.mod_data = 8'h33;
  assign array_if[1].output_modport.mod_data = 8'h44;
  assign array_if[1].output_modport.mod_data_arr[1] = 8'h66;

  initial begin
    #0;
    `checkh(array_if[0].data, 8'h11);
    `checkh(array_if[1].data, 8'h22);
    `checkh(array_if[0].output_modport.mod_data, 8'h33);
    `checkh(array_if[1].output_modport.mod_data, 8'h44);
    `checkh(array_if[0].output_modport.mod_data_arr[0], 8'h55);
    `checkh(array_if[1].output_modport.mod_data_arr[1], 8'h66);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
