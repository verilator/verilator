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
int nd = 0;

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

    // Additional regression: join_any should also complete when disable kills a forked task
    fork
      increment_y();
      #1 disable increment_y;
    join_any
    #3;
    if (y != 1) $stop;

    // Additional regression: named-block disable with join
    fork
      begin : worker_join
        z++;
        #2;
        z++;
      end
      #1 disable worker_join;
    join
    if (z != 1) $stop;

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
    if (w != 1) $stop;

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
    if (jf != 1) $stop;

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
    if (ddj != 0) $stop;

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
    if (ddja != 0) $stop;

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
    if (ddjn != 0) $stop;

    // disable after target is already finished (join)
    fork
      begin : done_join
        #1;
        dj_done = 1;
      end
    join
    disable done_join;
    if (dj_done != 1) $stop;

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
    if (dja_done != 1) $stop;

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
    if (djn_done != 1) $stop;

    // competing disables in the same time slot targeting the same block
    fork
      begin : race_target
        #5;
        race_disable = 99;
      end
      #1 disable race_target;
      #1 disable race_target;
    join
    if (race_disable != 0) $stop;

    // nested descendants are disabled and outer join resumes
    begin : nested_disable
      fork
        begin
          fork
            begin
              #1;
              nd += 1;
            end
            begin
              #3;
              nd += 10;
            end
          join_none
          #5;
          nd += 100;
        end
        begin
          #2;
          disable nested_disable;
        end
      join_none
      #6;
      nd += 1000;
    end
    #8;
    if (nd != 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
