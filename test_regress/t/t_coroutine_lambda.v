// DESCRIPTION: Verilator: Coroutine call inside AstExprStmt lambda test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
interface cpu_if(input logic clk);
endinterface

package p;

virtual class WriterIf;
  virtual function void write(input int t);
  endfunction
endclass

class BlockingWriter;
  virtual cpu_if vif;
  task write(int t);
    @(posedge vif.clk);
  endtask
endclass

class WriterAdapter extends WriterIf;
  BlockingWriter m_impl;
  function new(BlockingWriter impl);
    m_impl = impl;
  endfunction
  function void write(input int t);
    m_impl.write(t);  // function -> task path
  endfunction
endclass

class QueueLike;
  WriterIf sink;
  mailbox #(int) m;
  function bit try_get(output int t);
    if (!m.try_get(t)) begin
    end
    sink.write(t);  // can become coroutine call
  endfunction
endclass

class DriverLike;
  QueueLike reqq;
  function void item_done();
    int t;
    if (reqq.try_get(t) == 0) begin
    end
  endfunction
endclass

endpackage

module t;
  import p::*;

  logic clk = 0;
  cpu_if vif(clk);

  always #1 clk = ~clk;

  initial begin
    BlockingWriter writer;
    WriterAdapter adapter;
    QueueLike reqq;
    DriverLike drv;

    writer = new();
    writer.vif = vif;
    adapter = new(writer);

    reqq = new();
    reqq.sink = adapter;

    drv = new();
    drv.reqq = reqq;
    drv.item_done();

    #2 $finish;
  end
endmodule
