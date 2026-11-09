// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Andrei Girjoaba
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A clocking block output on an interface signal that the design drives with
// a non-blocking assignment. The generated clocking drive runs at the clocking
// event plus the output skew only, so it is no combinational blocking
// assignment and must not raise BLKANDNBLK. A drive issued between two
// clocking events is applied at the next event plus the skew, after the
// non-blocking assignment of that event (IEEE 1800-2023 14.16).

interface ifc (
    input logic clk
);
  logic valid;
  logic ready;
  clocking cbm @(posedge clk);
    default input #1step output #1;
    input ready;
    output valid;
  endclocking
  clocking cbs @(posedge clk);
    default input #1step output #1;
    input valid;
    output ready;
  endclocking
endinterface

module dut (
    input logic clk,
    input logic rst,
    ifc i
);
  // The design toggles valid every cycle
  always @(posedge clk) begin
    if (rst) i.valid <= 1'b0;
    else i.valid <= ~i.valid;
  end
endmodule

class driver;
  virtual ifc vi;
  function new(virtual ifc vi);
    this.vi = vi;
  endfunction
  task reset_s;
    vi.cbs.ready <= 1'b0;
  endtask
  task drive_m;
    vi.cbm.valid <= 1'b1;
  endtask
endclass

module t;
  logic clk = 0;
  initial forever #5 clk = ~clk;
  logic rst = 1;
  ifc i (clk);
  dut u (
      .clk,
      .rst,
      .i
  );
  driver drv = new(i);

  initial begin
    drv.reset_s();  // applied at the clocking event t=5 plus the skew
    @(negedge clk) `checkh(i.ready, 1'b0);  // t=10
    rst = 0;
    @(negedge clk) `checkh(i.valid, 1'b1);  // t=20: toggled at t=15
    @(negedge clk) `checkh(i.valid, 1'b0);  // t=30
    @(negedge clk) `checkh(i.valid, 1'b1);  // t=40
    drv.drive_m();  // applied at the clocking event t=45 plus the skew
    @(negedge clk) `checkh(i.valid, 1'b1);  // t=50: the drive won over the toggle to 0
    @(negedge clk) `checkh(i.valid, 1'b0);  // t=60: toggled 1 -> 0 at t=55
    @(negedge clk) `checkh(i.valid, 1'b1);  // t=70
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
