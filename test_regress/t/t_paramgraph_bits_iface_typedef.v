// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// DESCRIPTION: Test for $bits() of interface typedef used as parameter value
// This reproduces the issue from axis_upsizer.sv:186
// The issue: $bits(op_pkt_t) where op_pkt_t is a typedef from an interface port
// can't be converted to constant because the PARAMTYPEDTYPE's dtype isn't resolved

// Interface with a packed struct typedef
interface axis_if #(
  parameter int DataWidth = 8
);
  typedef struct packed {
    logic [DataWidth-1:0] data;
    logic valid;
  } pkt_t;

  logic [DataWidth-1:0] tdata;
  logic tvalid;
  logic tready;

  modport initiator (output tdata, tvalid, input tready);
  modport target (input tdata, tvalid, output tready);
endinterface

// Simple buffer module that takes a width parameter
module skid_buffer #(
  parameter int p_width = 8
) (
  input logic clk,
  input logic [p_width-1:0] data_i,
  output logic [p_width-1:0] data_o
);
  always_ff @(posedge clk) data_o <= data_i;
endmodule

// Module that uses $bits() of an interface typedef as a parameter
module axis_upsizer #(
  parameter int p_has_skid = 1
) (
  input logic clk,
  axis_if.initiator op_io
);
  // Typedef from interface port
  typedef op_io.pkt_t op_pkt_t;

  op_pkt_t op_pkt_int;

  generate
    if (p_has_skid>0) begin : gen_skid
      op_pkt_t skid_src_pkt;

      // This is the problematic line - $bits(op_pkt_t) used as parameter
      // The PARAMTYPEDTYPE for op_pkt_t has REQUIREDTYPE that needs resolution
      skid_buffer #(.p_width($bits(op_pkt_t))) skid (
        .clk(clk),
        .data_i(op_pkt_int),
        .data_o(skid_src_pkt)
      );
    end
  endgenerate
endmodule

module top;
  logic clk;

  axis_if #(.DataWidth(32)) op_if();

  axis_upsizer #(.p_has_skid(1)) u_upsizer (
    .clk(clk),
    .op_io(op_if.initiator)
  );

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
