// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Issue #7203: virtual interface select from sub-interface instance.
// The original reproducer: vip_agent holds vip_vif; vip_driver selects
// agent.vif.tx (a vip_tx_if sub-interface) into tx_vif.

interface vip_tx_if (
    output reg Tx
);
endinterface

interface vip_if (
    output reg Tx
);
  vip_tx_if tx (Tx);
endinterface

package vip_pkg;
  typedef virtual vip_if vip_vif;
  typedef virtual vip_tx_if vip_tx_vif;

  class vip_agent;
    vip_vif vif;
  endclass

  class vip_driver;
    vip_vif vif;
    vip_tx_vif tx_vif;
    virtual function void build_phase(vip_agent agent);
      // Sub-interface select: dtype(agent.vif) -> vip_vif -> vip_if
      vif = agent.vif;
      tx_vif = agent.vif.tx;
    endfunction
    // Chained member access through sub-interface
    virtual function void drive(logic val);
      vif.tx.Tx = val;
    endfunction
  endclass
endpackage

module t;
  logic wire_Tx;
  vip_if vif_inst (.Tx(wire_Tx));

  initial begin
    automatic vip_pkg::vip_agent agent = new;
    automatic vip_pkg::vip_driver driver = new;

    agent.vif = vif_inst;
    driver.vif = vif_inst;

    // Test 1 (issue reproducer): sub-interface select compiles and runs
    driver.build_phase(agent);

    // Test 2: tx_vif now points to the sub-interface; write through it
    driver.tx_vif.Tx = 1'b1;
    `checkd(wire_Tx, 1'b1)

    // Test 3: chained member write through virtual interface
    driver.drive(1'b0);
    `checkd(wire_Tx, 1'b0)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
