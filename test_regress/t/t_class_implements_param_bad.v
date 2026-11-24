// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Missing implementations when a base class is parameterized

interface class top_if;
  pure virtual function int get_a();
endclass

class param_cls #(type T = int);
  virtual function int get_b();
    return 1;
  endfunction
endclass

// Bad: parameterized base class has no get_a
class from_param_cls extends param_cls #(int) implements top_if;
endclass

class pass_param_cls extends param_cls #(int);
endclass

// Bad: base of base class is parameterized and has no get_a
class from_pass_param_cls extends pass_param_cls implements top_if;
endclass

// Bad: derived class is parameterized too
class param_from_param_cls #(int N = 1) extends param_cls #(int) implements top_if;
endclass

// Bad: parameterized interface class not implemented
interface class param_if #(type T = int);
  pure virtual function T get_c();
endclass

class from_param_if extends param_cls #(int) implements param_if #(int);
endclass

// Bad: pure virtual method and pure constraint of a parameterized virtual class not implemented
virtual class abstract_param_cls #(type T = int);
  pure virtual function int get_d();
  pure constraint cons;
endclass

class from_abstract_param_cls extends abstract_param_cls #(int);
endclass

// Bad: only implements a parameterized interface class
class only_param_if implements param_if #(int);
endclass

// Bad: inherited interface class methods conflict (IEEE 1800-2023 8.26.6.1)
interface class e1_if;
  pure virtual function int get_e();
endclass

interface class e2_if;
  pure virtual function int get_e();
endclass

virtual class conflict_param_cls extends param_cls #(int) implements e1_if, e2_if;
endclass

module t;
  from_param_cls c1 = new;
  from_pass_param_cls c2 = new;
  param_from_param_cls #(2) c3 = new;
  from_param_if c4 = new;
  from_abstract_param_cls c5 = new;
endmodule
