// DESCRIPTION: Verilator: Get parameter from modport interface
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface intf #(
    parameter int ITEM_QTY = 1
);
  logic item;

  modport source(input item);
endinterface

module pass_through (
    intf.source in_port,
    output logic [31:0] item_qty
);
  intf #(.ITEM_QTY(in_port.ITEM_QTY)) internal_port ();

  if (internal_port.ITEM_QTY == 1) begin : g_saw_default_item_qty
    $error("generate if evaluated internal_port.ITEM_QTY as interface default 1");
  end
  else if (internal_port.ITEM_QTY != 20) begin : g_bad_item_qty
    $error("generate if evaluated internal_port.ITEM_QTY as neither 1 nor 20");
  end

  assign internal_port.item = in_port.item;
  assign item_qty = internal_port.ITEM_QTY + internal_port.item;
endmodule

module t;
  intf #(.ITEM_QTY(20)) in_port ();

  logic [31:0] item_qty;

  assign in_port.item = 1'b0;

  pass_through dut (
      .in_port(in_port),
      .item_qty(item_qty)
  );

  initial begin
    `checkd(item_qty, 20);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
