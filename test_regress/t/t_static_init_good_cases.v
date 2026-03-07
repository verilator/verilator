// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Synder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

package p_cfg;
  class CmdProc;
    static CmdProc m_inst = new();
    static function CmdProc get_inst();
      return m_inst;
    endfunction
  endclass

  class Root;
    static Root m_inst = new();
    static bit m_set_cl_verb = (CmdProc::get_inst() != null);
    static function Root get();
      return m_inst;
    endfunction
  endclass
endpackage

module t;
  import p_cfg::*;

  class Carg;
    int v;
    function new(int val);
      v = val;
    endfunction
  endclass

  class CrvObj;
    rand int x;
  endclass

  function automatic int mk_range();
    return $urandom_range(100, 200);
  endfunction

  function automatic CrvObj mk_crv_obj();
    CrvObj h = new();
    if (h.randomize() == 0) begin
      $fatal(1, "class randomize failed");
    end
    return h;
  endfunction

  function automatic int mk_std_rand_or_default(output bit ok);
    int tmp;
    ok = (std::randomize(tmp) with { tmp inside {[20:25]}; } != 0);
    if (!ok) return -1;
    return tmp;
  endfunction

  function automatic int mk_file_for_read();
    int wh;
    int rh;
    wh = $fopen("t_static_init_good_cases_seed.txt", "w");
    if (wh == 0) return 0;
    $fwrite(wh, "Z");
    $fclose(wh);
    rh = $fopen("t_static_init_good_cases_seed.txt", "r");
    return rh;
  endfunction

  int seed_a = $urandom;
  int seed_b = $urandom_range(3, 9);
  int agg_arr[0:2] = '{seed_b, seed_b + 1, seed_b + 2};
  Carg carg_h = new(seed_b);
  std::mailbox #(int) mb = new();
  std::semaphore sem = new(2);
  int func_val = mk_range();
  int dep_val = func_val + 1;
  CrvObj crv_h = mk_crv_obj();
  int dyn_arr[] = new[3];
  bit std_rand_ok;
  int std_rand_val = mk_std_rand_or_default(std_rand_ok);
  int file_h = mk_file_for_read();
  int file_first_ch = $fgetc(file_h);
  int log_h = $fopen("t_static_init_good_cases.log", "w");

  initial begin
    int got;
    dyn_arr[0] = 11;
    dyn_arr[1] = 22;
    dyn_arr[2] = 33;

    if (CmdProc::get_inst() == null) $stop;
    if (Root::get() == null) $stop;
    if (Root::m_set_cl_verb != 1) $stop;

    if (seed_a === 'x) $stop;
    if (seed_b < 3 || seed_b > 9) $stop;
    if (carg_h == null) $stop;
    if (carg_h.v != seed_b) $stop;

    mb.put(55);
    mb.get(got);
    if (got != 55) $stop;
    if (sem.try_get(2) == 0) $stop;

    if (func_val < 100 || func_val > 200) $stop;
    if (dep_val != func_val + 1) $stop;
    if (crv_h == null) $stop;
    if (crv_h.x === 'x) $stop;
    if (dyn_arr.size() != 3) $stop;
    if (dyn_arr[0] != 11 || dyn_arr[1] != 22 || dyn_arr[2] != 33) $stop;

    // Solver-backed std::randomize may fail on systems without solver support.
    if (std_rand_ok) begin
      if (std_rand_val < 20 || std_rand_val > 25) $stop;
    end else begin
      if (std_rand_val != -1) $stop;
    end

    if (file_h == 0) $stop;
    if (file_first_ch != 90) $stop;  // 'Z'
    $fclose(file_h);

    if (agg_arr[0] != seed_b) $stop;
    if (agg_arr[1] != seed_b + 1) $stop;
    if (agg_arr[2] != seed_b + 2) $stop;

    if (log_h == 0) $stop;
    $fdisplay(log_h, "ok");
    $fclose(log_h);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
