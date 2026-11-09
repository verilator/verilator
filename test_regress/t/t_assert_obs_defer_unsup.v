// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  event go;
  event task_assert_scheduled;
  int q[$];
  int digits = 1;

  task automatic shared_task(input bit suspend);
    if (!suspend) assert #0 (1) $display("REPORT");
    if (suspend) @go;
  endtask

  task disabled_task;
    assert #0 (1) $display("REPORT");
    disable disabled_task;
  endtask

  task disabled_assert_task;
    assert #0 (0)
    else $display("REPORT");
    ->task_assert_scheduled;
    #1;
  endtask

  initial begin
    fork
      disabled_assert_task();
    join_none
    @task_assert_scheduled;
    disable disabled_assert_task;
  end

  class C;
    function void check();
      assert #0 (1) $display("REPORT");
      cover #0 (1) $display("REPORT");
    endfunction
  endclass

  initial begin
    fork
      assert #0 (1) $display("REPORT");
    join_none
  end

  C obj;
  initial begin
    fork
      shared_task(1);
      begin
        #1;
        shared_task(0);
        ->go;
      end
    join
    disabled_task();
    obj = new;
    obj.check();
    assert #0 (1) q.delete();
    assert #0 (1) $timeformat(-9, digits, " ns", 0);
    digits = 3;
    #1;
    $finish;
  end
endmodule
