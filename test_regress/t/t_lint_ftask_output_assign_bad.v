// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input  logic in,
    output wire  wire_out,
    output logic reg_out
);
  function void set_f(output set_out, input set_in);
    set_out = 1;
  endfunction

  task set_task(output set_out, input set_in);
    set_out = 1;
  endtask

  always_comb begin : setCall
    set_f(wire_out, in);
    set_f(reg_out, in);
    set_task(wire_out, in);
    set_task(reg_out, in);
  end
endmodule
