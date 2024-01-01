// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface Bus;
  logic [15:0] data;
endinterface

module t;
  Bus intf1(), intf2();
  virtual Bus vif1 = intf1, vif2 = intf2;

  task assign_to_vif2();
    if ($c("0")) return;
    #1 vif2.data = 'hfafa; #1;
  endtask

  initial forever begin
    intf1.data = 'hdead;
    if ($c("1")) begin
      #1 vif2.data = 'hbeef; #1;
    end
    intf1.data = 'hcafe;
    if ($c("0")); else begin
      #1 vif2.data = 'hface; #1;
    end
    intf1.data = 'hfeed;
    while ($time < 5) begin
      #1 vif2.data = 'hdeed; #1;
    end
    intf1.data = 'hdeaf;
    assign_to_vif2;
    intf1.data = 'hbebe;
    #1 $write("*-* All Finished *-*\n");
    $finish;
  end

  always_comb if ($time < 9) $write("vif1.data==%h\n", vif1.data);
  always_comb if ($time < 9) $write("intf2.data==%h\n", intf2.data);
endmodule
