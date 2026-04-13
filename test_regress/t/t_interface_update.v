// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ShiftIf #(
    parameter integer WIDTH,
    parameter integer STAGE
);
  typedef struct packed {
    logic [WIDTH-1:0] data;
    logic valid;
  } reg_t;

  reg_t data;

  function automatic reg_t update(input reg_t noChange, input logic enable);
    return enable == 1 ? data : noChange;
  endfunction
endinterface

module automatic t #(
    parameter integer WIDTH = 8,
    parameter integer SHIFT_WIDTH = 2
) (
    input logic logic_clk_in,
    input logic sync_rst_in,
    input logic [WIDTH-1:0] dataIn,
    input logic validIn,
    input logic enableIn,
    output logic [WIDTH-1:0] dataOut,
    output logic validOut
);

  ShiftIf #(WIDTH, 0) shift[SHIFT_WIDTH:0] ();
  ShiftIf #(WIDTH, 1) shiftTmp1 ();
  ShiftIf #(WIDTH, 2) shiftTmp2 ();

  always_comb begin
    shift[SHIFT_WIDTH].data.data = dataIn;
    shift[SHIFT_WIDTH].data.valid = validIn;
  end

  for (genvar i = 0; i < SHIFT_WIDTH; ++i) begin
    ShiftIf #(WIDTH, i) newValue ();
    always_comb newValue.data = shift[i+1].data;

    always_ff @(posedge logic_clk_in) shift[i].data = newValue.update(shift[i].data, enableIn);

  end

  assign dataOut = shift[0].data.data;
  assign validOut = shift[0].data.valid;

endmodule
