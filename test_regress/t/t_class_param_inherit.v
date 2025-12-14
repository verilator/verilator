// DESCRIPTION: Verilator: Issue #6814 - Inherited type parameters
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Verilator Authors.
// SPDX-License-Identifier: CC0-1.0

// Test inherited type parameters from parameterized base classes

class uvm_sequence_item;
   int id;
endclass

class uvm_seq_item_pull_port #(type T1=uvm_sequence_item, type T2=T1);
   T1 item1;
   T2 item2;
endclass

class uvm_driver #(type REQ=uvm_sequence_item, type RSP=REQ);
   REQ req;
   RSP rsp;
   uvm_seq_item_pull_port #(REQ, RSP) seq_item_port;
endclass

class my_tx extends uvm_sequence_item;
   int data;
endclass

// DERIVED CLASS - using REQ/RSP to parameterize another class
class my_driver extends uvm_driver#(my_tx);
   REQ local_req;
   RSP local_rsp;
   // Issue #6814: Using inherited REQ/RSP as type parameters
   uvm_seq_item_pull_port #(REQ, RSP) axi_port;
endclass

module t;
   my_driver drv;
   initial begin
      drv = new;
      // Test that types are correct
      drv.local_req = new;
      drv.local_req.data = 42;
      drv.local_rsp = new;
      drv.local_rsp.data = 123;
      drv.axi_port = new;
      drv.axi_port.item1 = new;
      drv.axi_port.item1.data = 456;
      if (drv.local_req.data == 42 && drv.local_rsp.data == 123 &&
          drv.axi_port.item1.data == 456) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $write("ERROR: Type mismatch\n");
      end
      $finish;
   end
endmodule
