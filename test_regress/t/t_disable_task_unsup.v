// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

int x = 0;

task increment_x;
  x++;
  #2;
  x++;
endtask

class driver;
  int m_time = 0;

  task get_and_send();
    forever begin
      #10;
      m_time += 10;
    end
  endtask

  task post_shutdown_phase();
    disable get_and_send;
  endtask
endclass

module t;

  driver c;

  initial begin
    fork
      increment_x();
      #1 disable increment_x;
    join

    if (x != 1) $stop;

    c = new;
    fork
      c.get_and_send;
    join_none
    if (c.m_time != 0) $stop;

    #11;
    if ($time != 12) $stop;
    if (c.m_time != 10) $stop;

    #20;
    if ($time != 32) $stop;
    if (c.m_time != 30) $stop;
    c.post_shutdown_phase;

    #20;
    if ($time != 52) $stop;
    if (c.m_time != 30) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
