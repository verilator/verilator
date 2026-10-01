// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Saqib Khan
// SPDX-License-Identifier: CC0-1.0

// Wait on a clocking block event through a modport (#8403)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`timescale 1ns / 1ns

interface simple_if (
    input logic clk
);
  logic req;
  clocking mem_cb @(posedge clk);
    output req;
  endclocking
  clocking mon_cb @(negedge clk);
    input req;
  endclocking
  modport mem_mp(clocking mem_cb);
  modport mon_mp(clocking mon_cb);
endinterface

module via_mp (
    simple_if.mem_mp p,
    simple_if.mon_mp m
);
  int mem_count = 0;
  int mon_count = 0;

  task automatic wait_mon();
    @(m.mon_cb);
  endtask

  initial begin
    repeat (3) begin
      @(p.mem_cb);
      mem_count++;
      $display("[%0t] mem_cb %0d", $time, mem_count);
    end
    p.mem_cb.req <= 1'b1;
  end

  initial begin
    repeat (3) begin
      wait_mon();
      mon_count++;
      $display("[%0t] mon_cb %0d", $time, mon_count);
    end
  end
endmodule

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  simple_if intf (.clk(clk));
  initial intf.req = 1'b0;

  via_mp u (
      .p(intf.mem_mp),
      .m(intf.mon_mp)
  );

  initial begin
    #100;
    `checkd(u.mem_count, 3);
    `checkd(u.mon_count, 3);
    `checkd(intf.req, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
