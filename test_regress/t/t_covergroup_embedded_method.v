// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

// Test an embedded covergroup calling methods of its enclosing class

package pkg;
  function automatic int pkg_val(int x);
    return x + 2;
  endfunction
endpackage

class Base;
  int offset = 1;
  function int base_val(int x);
    return x + offset;
  endfunction
endclass

class Cov extends Base;
  int state;
  static int s_offset = 1;
  function int get_val(int sel);
    return state + sel;
  endfunction
  function int get_zero();
    return state - 1;
  endfunction
  static function int s_val(int x);
    return x + s_offset;
  endfunction
  covergroup cg with function sample(int x);
    cp_method: coverpoint get_val(x) {bins b[] = {[0 : 3]};}
    cp_base: coverpoint base_val(x) {bins b[] = {[0 : 3]};}
    cp_iff: coverpoint x iff (get_val(x) == 3) {bins b[] = {[0 : 3]};}
    cp_noarg: coverpoint get_zero() {bins b[] = {[0 : 3]};}
    cp_static: coverpoint s_val(x) {bins b[] = {[0 : 3]};}
    cp_pkg: coverpoint pkg::pkg_val(x) {bins b[] = {[0 : 3]};}
    cp_own: coverpoint x iff (get_inst_coverage() >= 0.0) {bins b[] = {[0 : 3]};}
  endgroup
  covergroup cg2;
    cp_const: coverpoint get_val(0) {bins b[] = {[0 : 3]};}
  endgroup
  function new();
    cg = new;
    cg2 = new;
  endfunction
endclass

class ParamCov #(int W = 4);
  int state;
  function int get_val(int sel);
    return state + sel + W;
  endfunction
  covergroup cg with function sample(int x);
    cp_param: coverpoint get_val(x) {bins b[] = {[0 : 15]};}
  endgroup
  function new();
    cg = new;
  endfunction
endclass

module t;
  Cov c;
  ParamCov #(8) pc;
  initial begin
    c = new;
    c.state = 1;
    c.cg.sample(1);
    c.cg.sample(2);
    c.cg2.sample();
    pc = new;
    pc.cg.sample(1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
