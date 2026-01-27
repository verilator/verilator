// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off NORETURN
class c0 #(type T= real);
  static function T f();
  endfunction
endclass
class c2 #(type REQ=int, type RSP= int, type IMP=int);
  function new (IMP imp);
  endfunction
endclass
class c3 #(type REQ, type RSP, type IMP=RSP);
  function new (IMP imp);
  endfunction
endclass

class c1 #(type REQ= int, RSP=REQ);
  typedef c1 #( REQ , RSP) this_type;
  typedef c0 #(this_type) type_id;
  c2 #(REQ, RSP, this_type) c2inst;
  function new (string name, int parent);
    c2inst = new (this);
  endfunction

  c3 #(REQ, this_type) c3inst;
endclass

`define test \
c1 #(real) c1inst1;\
c1 #(real, real) c1inst2;\
c1 #(real, int) c1inst3;\
c1 #() c1inst4;\
c1 c1inst5;

`test
interface interf;
  // `test
endinterface
module t;
  // `test
  interf interf_inst();
endmodule
class topc;
  // `test
endclass

class paramcl;
endclass: paramcl
class c5;
c1 #(paramcl) seq;
function void f();
    seq = c1 #(paramcl)::type_id::f();
endfunction: f
endclass
c5 c5inst;
