// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
interface intf (
    input logic clk
);
  logic [7:0] sig;
  int id;

  clocking cb @(posedge clk);
    input sig;
  endclocking

  // Bound statically to ONE instance's clone; the clocking event, the
  // sampled 'sig', AND the non-constant default 'who = id' must all come
  // from the instance vif points to. Omitting 'who' at the call site
  // makes V3Width build a sample__Vtcwrap_* wrapper per scope, so this
  // also exercises dispatch + taskConnectWrap interaction.
  task automatic sample(output logic [7:0] got, output time t,
                        input int who = id);
    @(cb);
    got = cb.sig;
    t   = $time;
    // 'who' is defaulted inside the instance's wrapper clone; it must see
    // THAT instance's 'id', not the caller's or the last-linked one.
    if (who != id) $stop;
  endtask
endinterface

class Mon;
  virtual intf vif;
  task automatic run(output logic [7:0] got, output time t);
    vif.sample(got, t);   // 'who' omitted -> argWrap -> taskConnectWrap
  endtask
endclass

module t;
  logic clk_a = 0, clk_b = 0;

  intf if_a (.clk(clk_a));
  intf if_b (.clk(clk_b));

  always #5  clk_a = ~clk_a;   // posedges at 5, 15, 25...
  always #10 clk_b = ~clk_b;   // posedges at 10, 20, 30...

  initial begin
    automatic Mon ma = new;
    automatic Mon mb = new;
    automatic logic [7:0] ga, gb;
    automatic time ta, tb;

    if_a.sig = 8'haa;
    if_b.sig = 8'hbb;
    if_a.id  = 1;
    if_b.id  = 2;
    ma.vif = if_a;
    mb.vif = if_b;

    fork
      ma.run(ga, ta);
      mb.run(gb, tb);
    join

    $display("a: sig=%0x t=%0t   b: sig=%0x t=%0t", ga, ta, gb, tb);

    // Buggy binding: both calls wait on the last-linked instance's
    // clocking block -> wrong time and/or wrong sampled data. With the
    // potential wrap bug, 'who != id' inside the wrong instance's clone
    // also fires.
    if (ta != 5  || ga != 8'haa) $stop;
    if (tb != 10 || gb != 8'hbb) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
