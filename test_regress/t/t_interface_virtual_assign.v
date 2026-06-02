// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A continuous assign inside an interface must re-evaluate when the member it
// reads is written through a virtual interface (inside an interface subroutine
// invoked via a virtual interface handle).

interface my_if (input wire clk);
  logic [7:0] in_val = 0;
  logic [7:0] out_val;
  assign out_val = in_val;  // continuous assign reading an interface member

  // Same for an aggregate (packed-array) member, exercising the non-basic
  // value-change-trigger type path
  logic [1:0][7:0] in_arr = 0;
  logic [1:0][7:0] out_arr;
  assign out_arr = in_arr;

  task automatic drive(input logic [7:0] v);
    in_val <= v;
    in_arr <= {v, v};
    @(posedge clk);
  endtask
endinterface

class Driver;
  virtual my_if vif;
  function new(virtual my_if i);
    vif = i;
  endfunction
  task run(input logic [7:0] v);
    vif.drive(v);
  endtask
endclass

module t;
  logic clk = 0;
  initial forever #5 clk = ~clk;

  my_if  intf (.clk(clk));
  Driver d;

  initial begin
    d = new(intf);
    @(posedge clk);
    d.run(8'hA5);
    @(posedge clk);
    // Without a value-change trigger the assign never recomputes (out_val stays 0)
    if (intf.out_val !== 8'hA5) begin
      $write("%%Error: out_val=%0x exp=a5\n", intf.out_val);
      $stop;
    end
    if (intf.out_arr !== 16'hA5A5) begin
      $write("%%Error: out_arr=%0x exp=a5a5\n", intf.out_arr);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
