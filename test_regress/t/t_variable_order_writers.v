// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc;
  logic [7:0] data;
endinterface

module t (
    input clk
);
  // Parameter table, which is not model state
  localparam logic [31:0] TAB[4] = '{32'h11, 32'h22, 32'h33, 32'h44};

  // Accessed through a virtual interface, so it has an interface companion
  ifc tx ();
  virtual ifc vif;

  int cyc = 0;
  // Written by one block and read by all others
  logic [31:0] shared = 0;
  // Each element written by its own block
  logic [31:0] r[8] = '{default: 0};
  // The same computation in a single block, for checking
  logic [31:0] e[8] = '{default: 0};

  always @(posedge clk) begin
    cyc <= cyc + 1;
    shared <= shared + TAB[cyc[1:0]];
    vif = tx;
    vif.data <= cyc[7:0];
  end

  for (genvar k = 0; k < 8; ++k) begin : g
    always @(posedge clk) r[k] <= r[k] + (shared ^ TAB[r[k][1:0] ^ 2'(k)]);
  end

  always @(posedge clk) begin
    for (int k = 0; k < 8; ++k) e[k] <= e[k] + (shared ^ TAB[e[k][1:0] ^ 2'(k)]);
  end

  // Read on the other clock edge from the write through the virtual interface
  always @(negedge clk) begin
    if (cyc == 20) `checkh(tx.data, 8'd19);
  end

  always @(posedge clk) begin
    if (cyc == 20) begin
      for (int k = 0; k < 8; ++k) `checkh(r[k], e[k]);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
