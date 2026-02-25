// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

int x = 0;
int y = 0;
int z = 0;

int self_entry = 0;
int self_after_disable = 0;

int par_started = 0;
int par_finished = 0;
int par_parent_continued = 0;

class StaticCls;
  static int ticks = 0;

  static task run();
    forever begin
      #10;
      ticks++;
    end
  endtask

  static task stop();
    disable run;
  endtask
endclass

task increment_x;
  x++;
  #2;
  x++;
endtask

task increment_y;
  y++;
  #5;
  y++;
endtask

task finish_z;
  z++;
endtask

task self_stop;
  self_entry = 1;
  disable self_stop;
  self_after_disable = 1;
endtask

task worker;
  par_started++;
  #20;
  par_finished++;
endtask

task parent_disables_worker;
  fork
    worker();
    worker();
  join_none
  #5;
  disable worker;
  par_parent_continued = 1;
endtask

class Cls;
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

class NamedA;
  int v = 0;

  task run();
    forever begin
      #10;
      v++;
    end
  endtask

  task stop();
    disable run;
  endtask
endclass

class NamedB;
  int v = 0;

  task run();
    forever begin
      #10;
      v++;
    end
  endtask
endclass

class BaseNamed;
  int v = 0;

  task run();
    forever begin
      #10;
      v++;
    end
  endtask
endclass

class ChildNamed extends BaseNamed;
  int child_v = 0;

  task run();
    forever begin
      #10;
      child_v++;
    end
  endtask

  task stop();
    disable run;
  endtask
endclass

package PkgRun;
  int v = 0;

  task run();
    forever begin
      #10;
      v++;
    end
  endtask

  task stop();
    disable run;
  endtask
endpackage

interface Ifc;
  int v = 0;

  task run();
    forever begin
      #10;
      v++;
    end
  endtask

  task stop();
    disable run;
  endtask
endinterface

program Prog;
  int v = 0;

  task run();
    forever begin
      #10;
      v++;
    end
  endtask

  task stop();
    disable run;
  endtask
endprogram

module WorkerMod;
  int m = 0;

  task run();
    forever begin
      #10;
      m++;
    end
  endtask
endmodule

module t;
  Ifc ifc1();
  Prog prog1();
  WorkerMod mod1();

  initial begin
    automatic Cls c = new;
    automatic NamedA a = new;
    automatic NamedB b = new;
    automatic BaseNamed base_obj = new;
    automatic ChildNamed child_obj = new;
    int m_time_before_shutdown;
    int mod1_before;
    int a_before;
    int b_before;
    int static_before;
    int base_before;
    int child_before;
    int ifc_before;
    int prog_before;
    int pkg_before;

    // Module task disabled by sibling process in a fork
    fork
      increment_x();
      #1 disable increment_x;
    join_none
    #10;
    if (x != 1) $stop;
    // Re-disabling after prior disable (no active invocations) is a no-op
    disable increment_x;
    #1;
    if (x != 1) $stop;

    // Another basic module-task disable-by-name case
    fork
      increment_y();
      #3 disable increment_y;
    join_none
    #10;
    if (y != 1) $stop;

    // Disabling a task after it already finished is a no-op
    finish_z();
    if (z != 1) $stop;
    disable finish_z;
    #1;
    if (z != 1) $stop;

    // Self-disable in task by name
    self_stop();
    if (self_entry != 1) $stop;
    if (self_after_disable != 0) $stop;

    // Same task launched in parallel, disabled from parent task context
    parent_disables_worker();
    #30;
    if (par_started != 2) $stop;
    if (par_finished != 0) $stop;
    if (par_parent_continued != 1) $stop;

    // Same task launched in parallel, disabled from sibling process context
    par_started = 0;
    par_finished = 0;
    fork
      worker();
      worker();
      begin
        #5;
        disable worker;
      end
    join_none
    #30;
    if (par_started != 2) $stop;
    if (par_finished != 0) $stop;

    // Static class task disabled by name from another static task
    fork
      StaticCls::run();
      StaticCls::run();
    join_none
    #25;
    if (StaticCls::ticks == 0) $stop;
    static_before = StaticCls::ticks;
    StaticCls::stop();
    #30;
    if (StaticCls::ticks != static_before) $stop;

    // Same task name in different class scopes: disable only one scope
    fork
      a.run();
      b.run();
    join_none
    #25;
    if (a.v == 0 || b.v == 0) $stop;
    a_before = a.v;
    b_before = b.v;
    a.stop();
    #30;
    if (a.v != a_before) $stop;
    if (b.v <= b_before) $stop;

    // Same task name across inheritance scopes: disable only derived task
    fork
      base_obj.run();
      child_obj.run();
    join_none
    #25;
    if (base_obj.v == 0 || child_obj.child_v == 0) $stop;
    base_before = base_obj.v;
    child_before = child_obj.child_v;
    child_obj.stop();
    #30;
    if (child_obj.child_v != child_before) $stop;
    if (base_obj.v <= base_before) $stop;

    // Interface task disabled by name through interface scope
    fork
      ifc1.run();
    join_none
    #25;
    if (ifc1.v == 0) $stop;
    ifc_before = ifc1.v;
    ifc1.stop();
    #30;
    if (ifc1.v != ifc_before) $stop;

    // Program task disabled by name through program scope
    fork
      prog1.run();
    join_none
    #25;
    if (prog1.v == 0) $stop;
    prog_before = prog1.v;
    prog1.stop();
    #30;
    if (prog1.v != prog_before) $stop;

    // Package task disabled by name through package scope
    fork
      PkgRun::run();
    join_none
    #25;
    if (PkgRun::v == 0) $stop;
    pkg_before = PkgRun::v;
    PkgRun::stop();
    #30;
    if (PkgRun::v != pkg_before) $stop;

    // Dotted hierarchical task disable of module task by instance path
    fork
      mod1.run();
    join_none
    #25;
    if (mod1.m == 0) $stop;
    mod1_before = mod1.m;
    disable mod1.run;
    #30;
    if (mod1.m != mod1_before) $stop;

    // Class task disabled by name from outside that task
    fork
      c.get_and_send();
    join_none
    #35;
    if (c.m_time == 0) $fatal;
    m_time_before_shutdown = c.m_time;
    c.post_shutdown_phase();
    #30;
    if (c.m_time != m_time_before_shutdown) $fatal;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
