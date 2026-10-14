// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Packed variables marked with split_var, that cannot be bitblasted

// Not declared in a module
logic [7:0] unit_var  /*verilator split_var*/;

module t (
    input clk,
    // Primary input
    input [7:0] in  /*verilator split_var*/
);

  logic [63:0] crc = 64'h5aef0c8d_d70a4497;

  // Public
  logic [7:0] pub  /*verilator public*/  /*verilator split_var*/;
  // Variable index, warned in each context
  logic [7:0] vix  /*verilator split_var*/;
  // Written other than by an assignment, to multiple fragments
  logic [7:0] wro  /*verilator split_var*/;

  always_comb begin
    pub[3:0] = crc[3:0];
    pub[7:4] = crc[7:4];
    vix[3:0] = crc[3:0];
    vix[7:4] = crc[7:4];
    wro[3:0] = crc[3:0];
  end

  always @(posedge clk) begin
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    void'($sscanf("12", "%d", wro));
    $display("%x %x %x %x", in, pub, vix[crc[2:0]], wro);
    $display("%x", vix[crc[5:3]]);
  end

endmodule
