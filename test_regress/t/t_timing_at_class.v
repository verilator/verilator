// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  class apb_item;
    int addr;
    int data;
  endclass

  class any_monitor #(
      type REQ = int,
      RSP = REQ
  );

    REQ req;
    RSP rsp;
    int req_changes;
    int rsp_changes;

    task run_phase();
      $display("[%0t] run_phase", $time);
      fork
        forever begin
          @req;
          ++req_changes;
          $display("[%0t] req change #%0d", $time, req_changes);
        end
        forever begin
          @rsp;
          ++rsp_changes;
          $display("[%0t] rsp change #%0d", $time, rsp_changes);
        end
      join_none
    endtask

  endclass

  typedef int int_t;

  any_monitor #(int_t, int_t) imon;

  apb_item creq_item, crsp_item;
  any_monitor #(apb_item, apb_item) cmon;

  initial begin
    $display("Integer-based test");
    imon = new;
    #1;
    imon.run_phase();
    #1;
    imon.req = 1;  // Change
    imon.rsp = 2;  // Change
    #1;
    imon.req++;  // Change
    #1;
    `checkd(imon.req_changes, 2);
    `checkd(imon.rsp_changes, 1);

    $display("Class-based test");
    creq_item = new;
    crsp_item = new;
    cmon = new;
    #1;
    cmon.run_phase();
    #1;
    cmon.req = creq_item;  // Change
    cmon.rsp = crsp_item;  // Change
    #1;
    creq_item.addr++;  // Not a change
    #1;
    cmon.rsp = null;  // Change
    #1;
    `checkd(cmon.req_changes, 1);
    `checkd(cmon.rsp_changes, 2);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
