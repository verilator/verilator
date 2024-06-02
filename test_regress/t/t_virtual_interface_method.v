// Copyright 2003 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
// Create stimulus and Drive the interface
class DriverStim;
  protected virtual example_if v_if;

  task run();
    bit[7:0] x;
    bit[7:0] y;

    v_if.reset();
    forever begin
      x++;
      y++;

      $display("[DriverStim] initiating calculation, x: %8b y: %8b", x, y);
      v_if.initiate_calculation(x, y);
    end
  endtask: run

  function void bind_if(virtual example_if v_if);
    this.v_if = v_if;
  endfunction: bind_if
endclass: DriverStim
// Monitor returns from interface and check them
class MonitorCheck;
  localparam NUM_TXNS = 10;
  protected virtual example_if v_if;

  task run();
    logic[8:0] result;
    int txns_received = 0;

    forever begin
      v_if.wait_for_result(result);
      $display(
        "[MonitorCheck] (%d) result %7b carry_out %1b",
        txns_received, result[7:0], result[8]
        );
      if(++txns_received == NUM_TXNS)  begin
        $write("*-* All Finished *-*\n");
        $finish();
      end
    end
  endtask: run

  function void bind_if(virtual example_if v_if);
    this.v_if = v_if;
  endfunction: bind_if
endclass: MonitorCheck

module example(
  input  logic clk,
  input  logic rstn,
  input  logic[7:0] x,
  input  logic[7:0] y,
  output logic[8:0] z
  );

  // 8 bit full adder
  always_ff @(posedge clk)
    if(!rstn) z <= '0;
    else      z <= x + y;
endmodule: example
// interfaces with the DUT

interface example_if();
  localparam CLK_FREQ_MHz = 400;
  localparam CLK_PERIOD   = 1/((CLK_FREQ_MHz * 1e6) * (1e-12));

  logic      clk;
  logic      rstn;
  logic[7:0] x;
  logic[7:0] y;
  logic[8:0] z;

  initial begin: clk_gen
    forever #(CLK_PERIOD/2) clk = !clk;
  end: clk_gen

  task reset();
    $display("reset called");
    rstn = 0;
    @(posedge clk);
    $display("clock tick");
    rstn = 1;
    @(posedge clk);
  endtask: reset

  event calc_clkd;
  task initiate_calculation(
    input logic[7:0] x_in,
    input logic[7:0] y_in
    );

    x = x_in;
    y = y_in;
    @(posedge clk);
    ->calc_clkd;
  endtask: initiate_calculation

  task wait_for_result(output logic[8:0] result);
    @(calc_clkd);
    result = z;
  endtask: wait_for_result
endinterface: example_if

module t(/*AUTOARG*/);

  example_if example_if_inst();

  example DUT(
    .clk (example_if_inst.clk),
    .rstn(example_if_inst.rstn),
    .x   (example_if_inst.x),
    .y   (example_if_inst.y),
    .z   (example_if_inst.z)
    );


  initial begin: main
    DriverStim   driverStim = new();
    MonitorCheck monitorCheck = new();

    driverStim.bind_if(example_if_inst);
    monitorCheck.bind_if(example_if_inst);

    fork
      driverStim.run();
      monitorCheck.run();
    join_none
  end: main
endmodule: t
