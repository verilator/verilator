// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  int value;
  extern function int ext_f_np;
  extern function int ext_f_p();
  extern function int ext_f_i(int in);
  extern function ext_f_imp(in);
  extern static function int get_1();
  extern task ext_t_np;
  extern task ext_t_p();
  extern task ext_t_i(int in);
  class SubCls;
    int value;
    extern function int ext_f_np;
    extern function int ext_f_p();
    extern function int ext_f_i(int in);
    extern static function int get_10();
    extern task ext_t_np;
    extern task ext_t_p();
    extern task ext_t_i(int in);
  endclass
endclass

function int Cls::ext_f_np;
  return 1;
endfunction

function int Cls::ext_f_p();
  return value;
endfunction

function int Cls::ext_f_i(int in);
  return in+1;
endfunction

function Cls::ext_f_imp(in);
  return ~in;
endfunction

function int Cls::get_1();
  return 1;
endfunction

task Cls::ext_t_np();
  $write("*-* All Finished *-*\n");
endtask
task Cls::ext_t_p();
  $finish;
endtask
task Cls::ext_t_i(int in);
  if (in != 2) $stop;
  value = in;
endtask

function int Cls::SubCls::ext_f_np;
  return 10;
endfunction

function int Cls::SubCls::ext_f_p();
  return value;
endfunction

function int Cls::SubCls::ext_f_i(int in);
  return in+10;
endfunction

function int Cls::SubCls::get_10();
  return 10;
endfunction

task Cls::SubCls::ext_t_np();
  $write("Cls::SubCls::ext_t_np\n");
endtask
task Cls::SubCls::ext_t_p();
  $write("Cls::SubCls::ext_t_p\n");
endtask
task Cls::SubCls::ext_t_i(int in);
  if (in != 20) $stop;
  value = in;
endtask

// Each class has a foreach in a method defined in the class body and in one
// defined out-of-block, so their unnamed blocks get the same name

class CDyn;  // Dynamic array, out-of-block task
  int a[];
  task reset();
    foreach (a[i]) a[i] = 0;
  endtask
  extern task run();
endclass
task CDyn::run();
  foreach (a[i]) a[i] += i + 1;
endtask

package pkg_queue;
  class CQueue;  // Queue, out-of-block function
    int q[$];
    function void reset();
      foreach (q[i]) q[i] = 0;
    endfunction
    extern function int run();
  endclass
  function int CQueue::run();
    int sum = 0;
    foreach (q[i]) begin
      q[i]++;
      sum += q[i];
    end
    q.delete();
    return sum;
  endfunction
endpackage

package pkg_assoc;
  class CAssoc;  // Associative array
    int m[string];
    task reset();
      foreach (m[k]) m[k] = 0;
    endtask
    extern task run();
  endclass
  task CAssoc::run();
    foreach (m[k]) m[k] += k.len();
  endtask
endpackage

package pkg_string;
  class CString;  // String
    string s;
    task reset();
      foreach (s[j]) s[j] = "a";
    endtask
    extern task run();
  endclass
  task CString::run();
    foreach (s[j]) s[j] = s[j] + 8'(j);
  endtask
endpackage

module t;
  initial begin
    automatic Cls c = new;
    automatic Cls::SubCls subc = new;
    automatic CDyn cdyn = new;
    automatic pkg_queue::CQueue cqueue = new;
    automatic pkg_assoc::CAssoc cassoc = new;
    automatic pkg_string::CString cstring = new;

    cdyn.a = '{5, 6, 7};
    cdyn.reset();
    cdyn.run();
    if (cdyn.a[0] != 1) $stop;
    if (cdyn.a[2] != 3) $stop;

    cqueue.q.push_back(4);
    cqueue.q.push_back(9);
    cqueue.reset();
    if (cqueue.run() != 2) $stop;
    if (cqueue.q.size() != 0) $stop;

    cassoc.m["x"] = 4;
    cassoc.m["yyy"] = 4;
    cassoc.reset();
    cassoc.run();
    if (cassoc.m["x"] != 1) $stop;
    if (cassoc.m["yyy"] != 3) $stop;

    cstring.s = "zzz";
    cstring.reset();
    cstring.run();
    if (cstring.s != "abc") $stop;

    c.ext_t_i(2);
    if (c.ext_f_np() != 1) $stop;
    if (c.ext_f_p() != 2) $stop;
    if (c.ext_f_i(10) != 11) $stop;
    if (c.ext_f_imp(1'b1) != 1'b0) $stop;
    if (Cls::get_1() != 1) $stop;
    subc.ext_t_i(20);
    if (subc.ext_f_np() != 10) $stop;
    if (subc.ext_f_p() != 20) $stop;
    if (subc.ext_f_i(11) != 21) $stop;
    if (Cls::SubCls::get_10() != 10) $stop;
    subc.ext_t_np();
    subc.ext_t_p();
    c.ext_t_np();
    c.ext_t_p();
  end
endmodule
