// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  covergroup param_cg with function sample(bit sampled_param);
    param_cp: coverpoint sampled_param;
  endgroup

  bit sampled_value;
  covergroup value_cg with function sample(bit sampled_value);
    value_cp: coverpoint sampled_value;
  endgroup

  covergroup no_cg (input no_input_param) with function sample(bit no_sampled_param);
  endgroup

  initial begin
    static param_cg coverage1 = new();
    static value_cg coverage2 = new();
    sampled_value = 0;

    coverage1.sample(sampled_value);
    coverage1.sample(1'b1);

    coverage2.sample(sampled_value);
    coverage2.sample(1'b1);

    $finish;
  end
endmodule
