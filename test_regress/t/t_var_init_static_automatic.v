// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end
`define checkd_elab(gotv,expv) if ((gotv) !== (expv)) begin $error("%%Error: %s:%0d:  got=%0d exp=%0d", `__FILE__,`__LINE__, (gotv), (expv)); end
// verilog_format: on

class Cls;

  task tsk();
    for (int i = 0; i < 3; i++) begin
      /*automatic*/ int tj_auto;
      /*automatic*/ int tj_auto_init = 10;
      /*automatic*/ int tqueue_auto[$];
      /*automatic*/ int tqueue_auto_init[$] = '{1};
      static int tj_static;  // = 0
      static int tj_static_init = 10;
      static int tqueue_static[$];
      static int tqueue_static_init[$] = '{1};

      $display("Function iteration %0d:", i);
      tj_auto = tj_auto + 1;
      `checkd(tj_auto, 1);

      tj_auto_init = tj_auto_init + 1;
      `checkd(tj_auto_init, 11);

      `checkd(tqueue_auto.size(), 0);
      tqueue_auto.push_back(i + 10);
      `checkd(tqueue_auto.size(), 1);

      `checkd(tqueue_auto_init.size(), 1);
      tqueue_auto_init.push_back(i + 20);
      `checkd(tqueue_auto_init.size(), 2);

      tj_static = tj_static + 1;
      `checkd(tj_static, i + 1);

      tj_static_init = tj_static_init + 1;
      `checkd(tj_static_init, i + 1 + 10);

      tqueue_static.push_back(i + 20);
      `checkd(tqueue_static.size(), i + 1);

      tqueue_static_init.push_back(i + 20);
      `checkd(tqueue_static_init.size(), i + 2);
    end
  endtask

endclass

module t;

  function int func_const_kj_init();
    int r;
    for (int i = 0; i < 3; i++) begin
      automatic int kj;
      automatic int kj_init = 10;

      kj = kj + 1;
      `checkd_elab(kj, 1);

      kj_init = kj_init + 1;
      `checkd_elab(kj_init, 11);
      r = kj_init;
    end
    return r;
  endfunction

  localparam FUNC_CONST_KJ_INIT = func_const_kj_init();

  task forked;
    automatic int forktop = 100;
    for (int i = 0; i < 3; i++) begin
      // fork declarations are executed before all parallel statements (IEEE 1800-2023 9.3.2)
      fork : f_named
        // Automatics-in-forks Verilator will move to a VDynScope class
        automatic int fj_auto;
        automatic int fj_auto_init = 10;
        automatic int fqueue_auto[$];
        automatic int fqueue_auto_init[$] = '{1};
        // Statics-in-forks will stay in the original task
        static int fj_static;  // = 0
        static int fj_static_init = 10;
        static int fqueue_static[$];
        static int fqueue_static_init[$] = '{1};
        begin
          $display("Fork iteration %0d:", i);
          ++forktop;

          fj_auto = fj_auto + 1;
          `checkd(fj_auto, 1);

          fj_auto_init = fj_auto_init + 1;
          `checkd(fj_auto_init, 11);

          `checkd(fqueue_auto.size(), 0);
          fqueue_auto.push_back(i + 10);
          `checkd(fqueue_auto.size(), 1);

          `checkd(fqueue_auto_init.size(), 1);
          fqueue_auto_init.push_back(i + 20);
          `checkd(fqueue_auto_init.size(), 2);

          fj_static = fj_static + 1;
          `checkd(fj_static, i + 1);

          fj_static_init = fj_static_init + 1;
          `checkd(fj_static_init, i + 1 + 10);

          fqueue_static.push_back(i + 20);
          `checkd(fqueue_static.size(), i + 1);

          fqueue_static_init.push_back(i + 20);
          `checkd(fqueue_static_init.size(), i + 2);
        end
      join
    end
    `checkd(forktop, 100 + 3);
  endtask

  task forked_begin;
    // fork declarations are executed before all parallel statements (IEEE 1800-2023 9.3.2)
    fork : f_named
      for (int i = 0; i < 3; i++) begin
        // Automatics-in-zorks Verilator will move to a VDynScope class
        automatic int zj_auto;
        automatic int zj_auto_init = 10;
        automatic int zqueue_auto[$];
        automatic int zqueue_auto_init[$] = '{1};
        // Statics-in-forks will stay in the original task
        static int zj_static;  // = 0
        static int zj_static_init = 10;
        static int zqueue_static[$];
        static int zqueue_static_init[$] = '{1};
        begin
          $display("Fork-begin iteration %0d:", i);

          zj_auto = zj_auto + 1;
          `checkd(zj_auto, 1);

          zj_auto_init = zj_auto_init + 1;
          `checkd(zj_auto_init, 11);

          `checkd(zqueue_auto.size(), 0);
          zqueue_auto.push_back(i + 10);
          `checkd(zqueue_auto.size(), 1);

          `checkd(zqueue_auto_init.size(), 1);
          zqueue_auto_init.push_back(i + 20);
          `checkd(zqueue_auto_init.size(), 2);

          zj_static = zj_static + 1;
          `checkd(zj_static, i + 1);

          zj_static_init = zj_static_init + 1;
          `checkd(zj_static_init, i + 1 + 10);

          zqueue_static.push_back(i + 20);
          `checkd(zqueue_static.size(), i + 1);

          zqueue_static_init.push_back(i + 20);
          `checkd(zqueue_static_init.size(), i + 2);
        end
      end
    join
  endtask

  initial begin
    Cls c;
    c = new();
    c.tsk();

    `checkd(FUNC_CONST_KJ_INIT, 11);

    for (int i = 0; i < 3; i++) begin : p_named
      automatic int pj_auto;
      automatic int pj_auto_init = 10;
      automatic int pqueue_auto[$];
      automatic int pqueue_auto_init[$] = '{1};
      static int pj_static;  // = 0
      static int pj_static_init = 10;
      static int pqueue_static[$];
      static int pqueue_static_init[$] = '{1};

      $display("Process iteration %0d:", i);
      pj_auto = pj_auto + 1;
      `checkd(pj_auto, 1);
      `checkd(p_named.pj_auto, 1);

      pj_auto_init = pj_auto_init + 1;
      `checkd(pj_auto_init, 11);

      `checkd(pqueue_auto.size(), 0);
      pqueue_auto.push_back(i + 10);
      `checkd(pqueue_auto.size(), 1);

      `checkd(pqueue_auto_init.size(), 1);
      pqueue_auto_init.push_back(i + 20);
      `checkd(pqueue_auto_init.size(), 2);

      pj_static = pj_static + 1;
      `checkd(pj_static, i + 1);

      pj_static_init = pj_static_init + 1;
      `checkd(pj_static_init, i + 1 + 10);

      pqueue_static.push_back(i + 10);
      `checkd(pqueue_static.size(), i + 1);

      pqueue_static_init.push_back(i + 20);
      `checkd(pqueue_static_init.size(), i + 2);
    end

    forked();
    forked_begin();

    $finish;
  end

endmodule
