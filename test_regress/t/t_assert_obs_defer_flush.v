// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int external_disable_count;
  int fork_isolation_count;
  int branch_disable_count;
  int nested_disable_count;
  int inner_disable_count;
  event external_disable_ready;
  event fork_queue_ready;
  event branch_disable_ready;
  event inner_disable_ready;

  sub_flush u_sub ();

  initial begin : external_disable_victim
    #1;
    assert #0 (0)
    else record_external_disable();
    ->external_disable_ready;
    #10;
  end

  initial begin
    @external_disable_ready;
    disable external_disable_victim;
  end

  initial begin
    fork
      begin
        #1;
        assert #0 (0)
        else record_fork_isolation();
        ->fork_queue_ready;
      end
      begin
        @fork_queue_ready;
      end
    join
  end

  initial begin : branch_disable_owner
    fork
      begin : branch_disable_victim
        #1;
        assert #0 (0)
        else record_branch_disable();
        ->branch_disable_ready;
        #10;
      end
    join
  end

  initial begin
    @branch_disable_ready;
    disable branch_disable_owner.branch_disable_victim;
  end

  initial begin
    @u_sub.ready;
    disable u_sub.victim;
  end

  initial begin : nested_disable_victim
    #1;
    assert #0 (0)
    else record_nested_disable();
    fork
      disable nested_disable_victim;
    join
  end

  // Disabling a scope that is not the outermost one keeps the pending report
  initial begin : inner_disable_owner
    #1;
    begin : inner_disable_victim
      assert #0 (0)
      else record_inner_disable();
      ->inner_disable_ready;
      #10;
    end
  end

  initial begin
    @inner_disable_ready;
    disable inner_disable_owner.inner_disable_victim;
  end

  initial begin
    #3;
    `checkd(fork_isolation_count, 1);
    `checkd(external_disable_count, 0);
    `checkd(branch_disable_count, 0);
    `checkd(u_sub.count, 0);
    `checkd(nested_disable_count, 0);
    `checkd(inner_disable_count, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  function void record_external_disable();
    external_disable_count++;
    return;
  endfunction

  function void record_fork_isolation();
    fork_isolation_count++;
    return;
  endfunction

  function void record_branch_disable();
    branch_disable_count++;
  endfunction

  function void record_nested_disable();
    nested_disable_count++;
  endfunction

  function void record_inner_disable();
    inner_disable_count++;
  endfunction
endmodule

module sub_flush;
  int count;
  event ready;

  initial begin : victim
    #1;
    assert #0 (0)
    else record();
    ->ready;
    #10;
  end

  function void record();
    count++;
  endfunction
endmodule
