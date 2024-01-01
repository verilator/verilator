// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface Bus1;
  logic [15:0] data;
endinterface
interface Bus2;
  logic [15:0] data;
endinterface
interface Bus3;
  logic [15:0] data;
endinterface

module t (
    clk
);
  input clk;
  integer cyc = 0;
  Bus1 intf1();
  Bus2 intf2();
  Bus3 intf3(), intf4();
  virtual Bus1 vif1 = intf1;
  virtual Bus2 vif2 = intf2;
  virtual Bus3 vif3 = intf3, vif4 = intf4;

  // Finish on negedge so that $finish is last
  always @(negedge clk)
    if (cyc >= 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end

  function void assign_to_intf3();
    if ($c("1")) return;
    intf3.data = 'hcafe;
  endfunction

  always @(posedge clk) begin
    logic foo = 1;
    cyc <= cyc + 1;
    if (cyc == 1 || cyc == 3 || cyc == 5) intf1.data = 'hdead;
    else vif2.data = 'hbeef;
    if (cyc == 1 || cyc == 3 || cyc == 5) begin
      if (cyc >= 3) $c("// dummy statement");
      else intf3.data = 'hfafa;
      intf4.data = 'hface;
    end
    if (cyc == 7) begin
      while ($c("0")) begin
        foo = 0;
        intf3.data = 'hbebe;
      end
      intf4.data = 'hcafe;
    end
    if (cyc == 9) begin
      assign_to_intf3;
      intf4.data = 'hdeaf;
    end
  end

  always_comb $write("[%0t] vif1.data==%h\n", $time, vif1.data);
  always_comb $write("[%0t] intf2.data==%h\n", $time, intf2.data);
  always_comb $write("[%0t] vif4.data==%h\n", $time, vif4.data);
endmodule
