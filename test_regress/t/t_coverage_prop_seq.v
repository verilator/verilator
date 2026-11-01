// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 1'b0;
  // verilog_format: off
  property c_prop;
    @(negedge clk)
    1'b1;
  endproperty : c_prop

  property asrt_prop;
    @(negedge clk)
    1'b1;
  endproperty : asrt_prop

  property assm_prop;
    @(negedge clk)
    1'b1;
  endproperty : assm_prop

  sequence seq;
    1'b1;
  endsequence : seq

  property prop_seq;
    @(negedge clk) seq;
  endproperty : prop_seq

  property inner_prop;
    @(negedge clk)
    1'b1;
  endproperty : inner_prop

  property outer_prop;
    inner_prop;
  endproperty : outer_prop

  cover property (c_prop);
  assert property (asrt_prop);
  assume property (assm_prop);
  cover property (prop_seq);
  cover property (outer_prop);

  always #1 clk = ~clk;

  initial begin
    repeat (3) @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  // Ports and local variables of properties and sequences get no toggle coverage (#8745)
  bit p_a;
  bit p_c;

  property port_prop(logic x);
    @(negedge clk)
    x || !x;
  endproperty : port_prop

  property local_prop;
    logic snap;
    @(negedge clk)
    (1, snap = p_c) |-> (snap == p_c);
  endproperty : local_prop

  sequence port_seq(logic y);
    y || !y;
  endsequence : port_seq

  property prop_port_seq;
    @(negedge clk) port_seq(p_a);
  endproperty : prop_port_seq

  cover property (port_prop(p_a));
  cover property (local_prop);
  cover property (prop_port_seq);

endmodule
