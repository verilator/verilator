// DESCRIPTION: Verilator: Minimal UVM driver/sequence example
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Verilator Authors.
// SPDX-License-Identifier: CC0-1.0

// Minimal UVM example demonstrating:
// - UVM sequences with randomization
// - UVM driver with parameterized types
// - UVM factory
// - Basic TLM ports (seq_item_port)
// - UVM phasing

`include "uvm_macros.svh"

import uvm_pkg::*;

// Transaction class
class my_transaction extends uvm_sequence_item;
   rand bit [7:0] addr;
   rand bit [31:0] data;
   rand bit write;

   `uvm_object_utils_begin(my_transaction)
      `uvm_field_int(addr, UVM_ALL_ON)
      `uvm_field_int(data, UVM_ALL_ON)
      `uvm_field_int(write, UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name = "my_transaction");
      super.new(name);
   endfunction

   constraint addr_range { addr inside {[8'h00:8'hFF]}; }
   constraint data_range { data inside {[0:32'hFFFF]}; }
endclass

// Sequence class
class my_sequence extends uvm_sequence #(my_transaction);
   `uvm_object_utils(my_sequence)

   int num_items = 5;

   function new(string name = "my_sequence");
      super.new(name);
   endfunction

   virtual task body();
      my_transaction req;
      `uvm_info(get_type_name(), $sformatf("Starting sequence with %0d items", num_items), UVM_MEDIUM)
      for (int i = 0; i < num_items; i++) begin
         req = my_transaction::type_id::create($sformatf("req_%0d", i));
         start_item(req);
         // Simple randomization workaround for Verilator
         req.addr = $urandom_range(0, 255);
         req.data = $urandom_range(0, 65535);
         req.write = $urandom_range(0, 1);
         finish_item(req);
         `uvm_info(get_type_name(), $sformatf("Sent item[%0d]: addr=%h data=%h write=%b",
                   i, req.addr, req.data, req.write), UVM_MEDIUM)
      end
      `uvm_info(get_type_name(), "Sequence completed", UVM_MEDIUM)
   endtask
endclass

// Driver class using inherited type parameters (tests #6814 fix)
class my_driver extends uvm_driver #(my_transaction);
   `uvm_component_utils(my_driver)

   // Using inherited REQ type parameter
   REQ local_req;
   int items_driven = 0;

   function new(string name = "my_driver", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   virtual task run_phase(uvm_phase phase);
      `uvm_info(get_type_name(), "Driver run_phase started", UVM_MEDIUM)
      forever begin
         seq_item_port.get_next_item(req);
         drive_item(req);
         seq_item_port.item_done();
      end
   endtask

   virtual task drive_item(REQ item);
      items_driven++;
      `uvm_info(get_type_name(), $sformatf("Driving item[%0d]: addr=%h data=%h write=%b",
                items_driven, item.addr, item.data, item.write), UVM_MEDIUM)
      // Simulate some processing time
      #10ns;
   endtask

   function void report_phase(uvm_phase phase);
      `uvm_info(get_type_name(), $sformatf("Driver completed: %0d items driven", items_driven), UVM_MEDIUM)
   endfunction
endclass

// Agent class
class my_agent extends uvm_agent;
   `uvm_component_utils(my_agent)

   my_driver drv;
   uvm_sequencer #(my_transaction) seqr;

   function new(string name = "my_agent", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      drv = my_driver::type_id::create("drv", this);
      seqr = uvm_sequencer#(my_transaction)::type_id::create("seqr", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      drv.seq_item_port.connect(seqr.seq_item_export);
   endfunction
endclass

// Environment class
class my_env extends uvm_env;
   `uvm_component_utils(my_env)

   my_agent agent;

   function new(string name = "my_env", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agent = my_agent::type_id::create("agent", this);
   endfunction
endclass

// Test class
class my_test extends uvm_test;
   `uvm_component_utils(my_test)

   my_env env;

   function new(string name = "my_test", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      env = my_env::type_id::create("env", this);
   endfunction

   task run_phase(uvm_phase phase);
      my_sequence seq;
      phase.raise_objection(this);
      `uvm_info(get_type_name(), "Starting test", UVM_MEDIUM)

      seq = my_sequence::type_id::create("seq");
      seq.num_items = 5;
      seq.start(env.agent.seqr);

      `uvm_info(get_type_name(), "Test sequence completed", UVM_MEDIUM)
      phase.drop_objection(this);
   endtask

   function void report_phase(uvm_phase phase);
      `uvm_info(get_type_name(), "Test completed successfully!", UVM_NONE)
   endfunction
endclass

// Top module
module t;
   initial begin
      run_test("my_test");
   end

   // End simulation after test completes
   initial begin
      #1000ns;
      if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0 &&
          uvm_report_server::get_server().get_severity_count(UVM_FATAL) == 0) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $write("TEST FAILED\n");
      end
      $finish;
   end
endmodule
