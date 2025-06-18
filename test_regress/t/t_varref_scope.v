// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  logic read_data = 1;
  class seq_item;
    logic read_data;
  endclass
  class monitor_concrete;
    task monitor(seq_item item);
      item.read_data = read_data;
    endtask
  endclass
  initial begin
    monitor_concrete mon = new();
    seq_item item = new();
    mon.monitor(item);
    if (!item.read_data) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
