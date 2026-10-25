// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

package pin_pkg;
endpackage

class base #(
    type T = int
);
endclass

class holder #(
    type T = int
);
endclass

class derived extends base #(int);
  holder #(MISSING) value;
endclass

interface class interface_base #(
    type T = int
);
endclass

virtual class implemented_type implements interface_base #(int);
  holder #(T) value;
endclass

class nonclass_base #(
    type B = int
) extends B;
endclass

class nonclass_derived extends nonclass_base #(int);
  holder #(MISSING) value;
endclass

class pkg_qualified extends base #(int);
  typedef pin_pkg::missing_t missing_t;
  holder #(missing_t) value;
endclass

typedef class self_circular;
typedef class other_circular;

class circular_types;
  typedef self_circular::self_t self_t;
  typedef other_circular::other_t other_t;
endclass

// Base parameters using a name inherited from that base
class self_circular extends base #(circular_types::self_t);
  typedef T self_t;
endclass

class circular_user;
  holder #(other_circular::other_t) value;
endclass

class other_circular extends base #(circular_types::other_t);
  typedef T other_t;
endclass

class cycle_a extends cycle_b #(1);
  holder #(MISSING) value;
endclass

class cycle_b #(
    int N = 1
) extends cycle_a;
endclass

module t;
  derived d;
  implemented_type implemented;
  nonclass_derived nonclass;
  pkg_qualified qualified;
  self_circular self_circ;
  circular_user circ_user;
  cycle_a cycle;
endmodule
