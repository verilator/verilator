// DESCRIPTION: Verilator: Test hierarchical references through interface modports
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface nested_if;
  logic [7:0] d;
endinterface

interface data_if;
  logic [7:0] data;
  logic [7:0] mod_data;
  logic [7:0] mod_data_arr[2];
  modport output_modport(output mod_data, output mod_data_arr);
endinterface

module t;
  data_if array_if[2] ();
  data_if if_0 ();
  data_if if_1 ();

  assign array_if[0].data = 8'h11;
  assign array_if[1].data = 8'h22;
  assign array_if[0].output_modport.mod_data = 8'h33;
  assign array_if[1].output_modport.mod_data = 8'h44;
  assign array_if[1].output_modport.mod_data_arr[1] = 8'h44;

  assign if_0.data = 8'h55;
  assign if_1.data = 8'h66;
  assign if_0.output_modport.mod_data = 8'h77;
  assign if_1.output_modport.mod_data = 8'h88;

  initial begin
    #0;
    `checkh(array_if[0].data, 8'h11);
    `checkh(array_if[1].data, 8'h22);
    `checkh(array_if[0].output_modport.mod_data, 8'h33);
    `checkh(array_if[1].output_modport.mod_data, 8'h44);
    `checkh(array_if[1].output_modport.mod_data_arr[1], 8'h44);
    `checkh(if_0.data, 8'h55);
    `checkh(if_1.data, 8'h66);
    `checkh(if_0.output_modport.mod_data, 8'h77);
    `checkh(if_1.output_modport.mod_data, 8'h88);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
