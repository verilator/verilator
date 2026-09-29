// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ifc;
  logic [7:0] data;
endinterface
module t (
    input logic clk,
    input logic [7:0] i,
    output logic [7:0] ob
);
  ifc tx ();
  virtual ifc vif;
  logic [7:0] rb = 0;
  always @(posedge clk) begin
    vif = tx;
    vif.data = i;
  end
  always @(posedge clk) begin
    rb <= rb ^ i ^ 8'h5a;
  end
  assign ob = rb ^ tx.data;
endmodule
