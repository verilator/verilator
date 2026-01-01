// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

module t;
  event e_all_xfers_monitored_tx[4];
  event e_all_xfers_monitored_rx[4];
  event e_all_xfers_completed[4];

  task automatic debug(string s);
    $display("%s", s);
  endtask

  task run_traffic_per_port(int port_id);
    fork
      automatic int id = port_id;
      begin
        fork
          begin
            @(e_all_xfers_monitored_tx[id]);
            debug($sformatf("[%0t] [Port %0d] TX done", $time, id));
          end
          begin
            @(e_all_xfers_monitored_rx[id]);
            debug($sformatf("[%0t] [Port %0d] RX done", $time, id));
          end
        join

        ->e_all_xfers_completed[id];
        $display("[%0t] [Port %0d] ALL done", $time, id);
      end
    join_none
  endtask

  initial begin
    int i;

    for (i = 0; i < 2; i++) begin
      run_traffic_per_port(i);
    end

    #10->e_all_xfers_monitored_tx[0];
    #10->e_all_xfers_monitored_rx[0];

    #10->e_all_xfers_monitored_tx[1];
    #10->e_all_xfers_monitored_rx[1];

    @(e_all_xfers_completed[0]);
    @(e_all_xfers_completed[1]);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
