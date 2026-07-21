// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module unoptflat_process_split (
    input logic ptr_empty,
    input logic pop_en,
    output logic empty,
    output logic pop_qual
);
  always_comb begin
    empty = ptr_empty;
    pop_qual = pop_en && !empty;
  end
endmodule

module external_write_guard (
    input logic ptr_empty,
    output logic old_empty
);
  logic [1:0] empty;

  // An external write to empty[1] before evaluation must be visible to old_empty.
  // verilator lint_off UNOPTFLAT
  always @* begin
    empty[0] = ptr_empty;
    old_empty = empty[1];
  end
  // verilator lint_on UNOPTFLAT
endmodule

module unoptflat_array_output (
    input logic ptr_empty,
    input logic sink_ready,
    output logic ready,
    output logic transfer_ready,
    output logic [1:0] status[2]
);
  always_comb begin
    ready = ptr_empty;
    transfer_ready = ready && sink_ready;
    status[0] = {ready, transfer_ready};
    status[1] = {transfer_ready, ready};
  end
endmodule

module external_array_write_guard (
    input logic [1:0] new_status,
    output logic [1:0] old_status
);
  logic [1:0] status[1];

  // An external write to status[0][1] before evaluation must be visible to old_status.
  // verilator lint_off UNOPTFLAT
  always @* begin
    status[0][0] = ^new_status;
    old_status = status[0];
  end
  // verilator lint_on UNOPTFLAT
endmodule

module top (
    input logic ptr_empty,
    input logic input_valid,
    output logic pop_qual,
    output logic old_empty,
    output logic array_transfer_ready,
    output logic [1:0] old_status
);
  logic empty;
  logic pop_en;
  logic array_ready;
  logic array_sink_ready;
  logic [1:0] status[2];

  always_comb begin
    pop_en = 1'b0;
    if (!empty) pop_en = 1'b1;
  end

  unoptflat_process_split u_fifo_ctrl (
      .ptr_empty(ptr_empty),
      .pop_en(pop_en),
      .empty(empty),
      .pop_qual(pop_qual)
  );

  external_write_guard u_external_write_guard (
      .ptr_empty(ptr_empty),
      .old_empty(old_empty)
  );

  assign array_sink_ready = input_valid && array_ready;

  unoptflat_array_output u_array_output (
      .ptr_empty(ptr_empty),
      .sink_ready(array_sink_ready),
      .ready(array_ready),
      .transfer_ready(array_transfer_ready),
      .status(status)
  );

  external_array_write_guard u_external_array_write_guard (
      .new_status({ptr_empty, input_valid}),
      .old_status(old_status)
  );
endmodule
