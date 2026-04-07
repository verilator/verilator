// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); $stop; end while(0);
// verilog_format: on


class blocking_sequence;
  bit m_called;
  bit m_called_body;
  bit m_returned_body;
  bit m_returned;

  task body();
    m_called_body = 1;
    wait (0);
    m_returned_body = 1;
    $fatal(2, "did wait(0) - SHOULD NOT GET HERE");
  endtask

  task start();
    fork
      begin
        #0;
        m_called = 1;
        body();
        m_returned = 1;
        $fatal(2, "called body() - SHOULD NOT GET HERE");
        #0;
      end
    join
  endtask
endclass

module t;
  bit timeout;
  initial begin
    blocking_sequence b;
    b = new;
    fork
      begin
        b.start();
      end
      begin
        #10;
        timeout = 1;
      end
    join_any
    `checkh(b.m_called, 1);
    `checkh(b.m_called_body, 1);
    `checkh(b.m_returned, 0);
    `checkh(b.m_returned_body, 0);
    `checkh(timeout, 1);
    $finish;
  end

endmodule
