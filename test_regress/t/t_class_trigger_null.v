// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Cameron Waite.
// SPDX-License-Identifier: CC0-1.0

// Test for null pointer dereference when sensitivity expressions reference
// class members. Verilator evaluates trigger expressions at simulation start,
// even for tasks that haven't been called yet. This caused null pointer
// dereference when accessing class_handle.event or class_handle.vif.signal
// because the task parameter didn't have a valid value yet.
//
// Also tests "instant fall-through" scenario: events triggered at time 0
// (same timestep as class construction) should still be detected.

interface my_if;
  logic sig;
endinterface

package my_pkg;

  class my_driver;
    virtual my_if vif;
    event my_event;

    function new(virtual my_if vif_in);
      vif = vif_in;
    endfunction
  endclass

  // Task with sensitivity expressions on class member event and signals
  task automatic my_task(my_driver drv, output int ev_cnt, pos_cnt, neg_cnt);
    my_driver h = drv;

    if (h == null) begin
      $display("Error: drv is NULL!");
      $finish;
    end

    fork
      begin
        // Wait on class member event - previously caused null deref
        @(h.my_event);
        ev_cnt++;
      end
      begin
        // Wait on posedge through virtual interface - previously caused null deref
        @(posedge h.vif.sig);
        pos_cnt++;
      end
      begin
        // Wait on negedge through virtual interface - previously caused null deref
        @(negedge h.vif.sig);
        neg_cnt++;
      end
      begin
        #10;
        ->h.my_event;
        #10;
        h.vif.sig = 1;
        #10;
        h.vif.sig = 0;
      end
    join
  endtask

endpackage

module t;
  my_if intf ();
  my_pkg::my_driver drv;
  virtual my_if vif;

  int event_count;
  int posedge_count;
  int negedge_count;

  // Counter for instant (time 0) event detection
  int instant_event_count = 0;

  // Test "instant fall-through": sensitivity on class member event at module level
  // This always block is evaluated at elaboration when drv is still null.
  // After construction, events triggered at time 0 should still be detected.
  always @(drv.my_event) begin
    instant_event_count++;
  end

  // Construct the class at time 0
  initial begin
    vif = intf;
    drv = new(vif);
    intf.sig = 0;
  end

  // Trigger event at time 0 (same timestep as construction) - "instant fall-through"
  // Use #0 to ensure construction happens first in delta cycle ordering
  initial begin
    #0;
    ->drv.my_event;
  end

  // Call the task later - trigger expressions were evaluated before this
  initial begin
    event_count = 0;
    posedge_count = 0;
    negedge_count = 0;

    #20;
    my_pkg::my_task(drv, event_count, posedge_count, negedge_count);

    // Verify all triggers occurred
    if (event_count != 1) begin
      $display("%%Error: event_count = %0d, expected 1", event_count);
      $stop;
    end
    if (posedge_count != 1) begin
      $display("%%Error: posedge_count = %0d, expected 1", posedge_count);
      $stop;
    end
    if (negedge_count != 1) begin
      $display("%%Error: negedge_count = %0d, expected 1", negedge_count);
      $stop;
    end

    // Verify instant fall-through worked (time 0 event was detected)
    // We expect 2: one from time 0, one from the task at time 30
    if (instant_event_count != 2) begin
      $display("%%Error: instant_event_count = %0d, expected 2", instant_event_count);
      $display("%%Error: Instant fall-through failed - events at time 0 were missed!");
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
