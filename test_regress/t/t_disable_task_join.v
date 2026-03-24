// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

int x = 0;
int y = 0;
int z = 0;
int w = 0;
int jf = 0;
int ddj = 0;
int ddja = 0;
int ddjn = 0;
int dj_done = 0;
int dja_done = 0;
int djn_done = 0;
int race_disable = 0;

task increment_x;
  x++;
  #2;
  x++;
endtask

task increment_y;
  y++;
  #2;
  y++;
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
  task automatic progress(input string label);
    $display("DBG:t_disable_task_join:%s t=%0t x=%0d y=%0d z=%0d w=%0d m_time=%0d",
             label, $time, x, y, z, w, (c == null) ? -1 : c.m_time);
  endtask

  initial begin
    progress("start");
    fork
      increment_x();
      #1 disable increment_x;
    join

    if (x != 1) $fatal(1, "x=%0d expected 1", x);

    c = new;
    fork
      c.get_and_send;
    join_none
    if (c.m_time != 0) $fatal(1, "c.m_time=%0d expected 0 before first delay", c.m_time);

    #11;
    if ($time != 12) $fatal(1, "$time=%0t expected 12", $time);
    if (c.m_time != 10) $fatal(1, "c.m_time=%0d expected 10 after 11 ticks", c.m_time);

    #20;
    if ($time != 32) $fatal(1, "$time=%0t expected 32", $time);
    if (c.m_time != 30) $fatal(1, "c.m_time=%0d expected 30 before disable", c.m_time);
    c.post_shutdown_phase;

    #20;
    if ($time != 52) $fatal(1, "$time=%0t expected 52", $time);
    if (c.m_time != 30) $fatal(1, "c.m_time=%0d expected 30 after disable", c.m_time);
    progress("after_class_task_disable");

    // Additional regression: join_any should also complete when disable kills a forked task
    fork
      increment_y();
      #1 disable increment_y;
    join_any
    #3;
    if (y != 1) $fatal(1, "y=%0d expected 1", y);
    progress("after_join_any_task_disable");

    // Additional regression: named-block disable with join
    fork
      begin : worker_join
        z++;
        #2;
        z++;
      end
      #1 disable worker_join;
    join
    if (z != 1) $fatal(1, "z=%0d expected 1", z);
    progress("after_named_block_join_disable");

    // Additional regression: named-block disable with join_any
    fork
      begin : worker_join_any
        w++;
        #2;
        w++;
      end
      #1 disable worker_join_any;
    join_any
    #3;
    if (w != 1) $fatal(1, "w=%0d expected 1", w);
    progress("after_named_block_join_any_disable");

    // disable fork from inside a join_any branch
    fork
      begin
        fork
          begin
            #1;
            jf = 1;
          end
          begin
            #5;
            jf = 99;
          end
        join_none
        #2;
        disable fork;
      end
      begin
        #3;
      end
    join_any
    #6;
    if (jf != 1) $fatal(1, "jf=%0d expected 1", jf);
    progress("after_disable_fork");

    // multiple sequential disables of the same target under join
    fork
      begin : twice_join
        #5;
        ddj = 99;
      end
      begin
        #1 disable twice_join;
        #1 disable twice_join;
      end
    join
    if (ddj != 0) $fatal(1, "ddj=%0d expected 0", ddj);

    // multiple sequential disables of the same target under join_any
    fork
      begin : twice_join_any
        #5;
        ddja = 99;
      end
      begin
        #1 disable twice_join_any;
        #1 disable twice_join_any;
      end
    join_any
    #6;
    if (ddja != 0) $fatal(1, "ddja=%0d expected 0", ddja);

    // multiple sequential disables of the same target under join_none
    begin
      fork
        begin : twice_join_none
          #5;
          ddjn = 99;
        end
      join_none
      #1 disable twice_join_none;
      #1 disable twice_join_none;
      #6;
    end
    if (ddjn != 0) $fatal(1, "ddjn=%0d expected 0", ddjn);

    // disable after target is already finished (join)
    fork
      begin : done_join
        #1;
        dj_done = 1;
      end
    join
    disable done_join;
    if (dj_done != 1) $fatal(1, "dj_done=%0d expected 1", dj_done);

    // disable after target is already finished (join_any)
    fork
      begin : done_join_any
        #1;
        dja_done = 1;
      end
      #2;
    join_any
    #2;
    disable done_join_any;
    if (dja_done != 1) $fatal(1, "dja_done=%0d expected 1", dja_done);

    // disable after target is already finished (join_none)
    begin
      fork
        begin : done_join_none
          #1;
          djn_done = 1;
        end
      join_none
      #2;
      disable done_join_none;
      #1;
    end
    if (djn_done != 1) $fatal(1, "djn_done=%0d expected 1", djn_done);

    // competing disables in the same time slot targeting the same block
    fork
      begin : race_target
        #5;
        race_disable = 99;
      end
      #1 disable race_target;
      #1 disable race_target;
    join
    if (race_disable != 0) $fatal(1, "race_disable=%0d expected 0", race_disable);
    progress("after_race_disable");

    progress("before_finish");

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
