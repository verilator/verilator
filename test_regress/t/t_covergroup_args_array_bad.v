// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ParameterizedIf #(int WIDTH = 5);
  logic [WIDTH-1:0] value;
  modport monitor(input value);
  modport driver(output value);
endinterface

module t;
  virtual ParameterizedIf #(5).driver driver5[2];
  virtual ParameterizedIf #(6).monitor monitor6[2];

  covergroup cg_array_input(input virtual ParameterizedIf #(5).monitor vifs[2]);
    cp: coverpoint vifs[0].value;
  endgroup

  covergroup cg_array_ref(ref virtual ParameterizedIf #(5).monitor vifs[2]);
    cp: coverpoint vifs[0].value;
  endgroup

  covergroup cg_array_const_ref(const ref virtual ParameterizedIf #(5).monitor vifs[2]);
    cp: coverpoint vifs[0].value;
  endgroup

  cg_array_input bad_input_modport = new(driver5);
  cg_array_input bad_input_parameter = new(monitor6);
  cg_array_ref bad_ref_modport = new(driver5);
  cg_array_const_ref bad_const_ref_parameter = new(monitor6);
endmodule
