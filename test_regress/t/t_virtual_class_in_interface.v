//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// DESCRIPTION: Verilator: Verilog Test module
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

virtual class driver_class_virtual;
  virtual task send_data(logic [7:0] d);
  endtask
endclass

interface intf (input logic clk);
  logic [7:0] data;
  logic       valid;

  class driver_class extends driver_class_virtual;
    task send_data(logic [7:0] d);
      @(posedge clk);
      data  = d;
      valid = 1'b1;

      @(posedge clk);
      data  = '0;
      valid = 1'b0;
    endtask
  endclass

  // Instantiate the class object for this specific interface instance
  driver_class drv;

  function driver_class get_drv();
    drv = new();
    return drv;
  endfunction
endinterface

module t(
  input clk
);

  // Instantiate TWO distinct interfaces
  intf intf_1 (clk);
  intf intf_2 (clk);

  driver_class_virtual drv1;
  driver_class_virtual drv2;

  bit [7:0] intf_1_q [$];
  bit [7:0] intf_2_q [$];

  initial begin
    drv1 = intf_1.get_drv();
    drv2 = intf_2.get_drv();

    drv1.send_data(8'hAA);
    repeat(5) @(posedge clk);
    drv2.send_data(8'hBB);
    #20;
    `checks(intf_1_q[0],8'hAA);
    `checkh(intf_1_q.size(),1);
    `checks(intf_2_q[0],8'hBB);
    `checkh(intf_2_q.size(),1);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  // Monitor the outputs to verify independence
  always @(posedge clk) begin
    if (intf_1.valid) intf_1_q.push_back(intf_1.data);
    if (intf_2.valid) intf_2_q.push_back(intf_2.data);
  end

endmodule
