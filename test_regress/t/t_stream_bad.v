// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Geza Lore
// SPDX-License-Identifier: CC0-1.0

module t;

  logic [31:0] packed_data_32;
  byte byte_in[4];
  logic [3:0] x = 4'($random());

  initial begin
    packed_data_32 = {<<$random{byte_in}};
    packed_data_32 = {<<x{byte_in}};
  end

  // An inout port connection is not an assignment, so a stream is not valid
  wire [31:0] io_bus;
  sub_inout i_sub_inout (.io({>>{io_bus}}));

  // A ref port connection is a hierarchical reference, not an assignment,
  // so a stream is not valid
  logic [31:0] ref_var;
  sub_ref i_sub_ref (.r({>>{ref_var}}));

endmodule

module sub_inout (
    inout wire [31:0] io
);
endmodule

module sub_ref (
    ref logic [31:0] r
);
endmodule
