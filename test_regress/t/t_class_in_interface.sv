// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0`define stop $stop

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

interface interface_with_class (input logic clk);
    logic [7:0] data;
    logic       valid;

    // import driver_pkg::*;
      class driver_class;
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
    
    initial begin
        drv = new();
    end

endinterface


module test_tb4;
    logic clk = 0;
    
    // Generate a simple clock
    always #5 clk = ~clk;

    // Instantiate TWO distinct interfaces
    interface_with_class intf_1 (clk);
    interface_with_class intf_2 (clk);
    
    bit [7:0] intf_1_data_q [$];
    bit [7:0] intf_2_data_q [$];

    initial begin
        
        while(intf_1.drv == null)
          @(posedge clk);
        intf_1.drv.send_data(8'hAA);
        repeat(5) @(posedge clk);
        intf_2.drv.send_data(8'hBB);
        
        
        #20;
        `checks(intf_1_data_q[0],8'hAA);
        `checkh(intf_1_data_q.size(),1);
        `checks(intf_2_data_q[0],8'hBB);
        `checkh(intf_2_data_q.size(),1);
        $write("*-* All Finished *-*\n");
        $finish;
    end

    // Monitor the outputs to verify independence
    always @(posedge clk) begin
        if (intf_1.valid) 
          intf_1_data_q.push_back(intf_1.data);
        if (intf_2.valid) 
          intf_2_data_q.push_back(intf_2.data);
    end

endmodule