// DESCRIPTION: Verilator: Verilog Test module
//
// Passing a real interface array as a class new() argument bound to a
// virtual interface array formal parameter. Exercises the cell dearrayer's
// orphan-VarRef fixup in V3Inst.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

interface AXI_BUS_DV;
endinterface

package tb_axi_xbar_pkg;
  class axi_xbar_monitor #(
      parameter int unsigned NoMasters
  );
    int captured_count;
    function new(virtual AXI_BUS_DV axi_masters_vif[NoMasters-1:0]);
      captured_count = NoMasters;
    endfunction
  endclass
endpackage

module t;
  localparam int unsigned TbNumMasters = 32'd6;

  AXI_BUS_DV master_monitor_dv[TbNumMasters-1:0] ();

  initial begin
    static tb_axi_xbar_pkg::axi_xbar_monitor #(.NoMasters(TbNumMasters))
        monitor = new(master_monitor_dv);
    `checkh(monitor.captured_count, 32'd6);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
