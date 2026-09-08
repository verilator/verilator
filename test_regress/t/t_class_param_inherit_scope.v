// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

class constants #(
    int N = 1
);
  typedef bit [N-1:0] data_t;
endclass

class value_base #(
    int N = 1
);
  typedef bit [N-1:0] T;
endclass

class type_base #(
    type T = int
);
endclass

class local_base #(
    int N = 1
);
  local typedef bit [N-1:0] T;
endclass

class type_holder #(
    type T = int
);
  T value;
endclass

// Each inherited T is found through base parameters using other classes.
class scoped_value extends value_base #(constants #(7)::N);
  T value;
  type_holder #(T) holder;
endclass

class packed_range extends type_base #(bit [constants #(15)::N:1]);
  T value;
endclass

class bits_query extends value_base #($bits(
    constants #(31)::data_t
));
  T value;
endclass

class type_query #(
    int N = 33
) extends type_base #(type (constants #(N)::data_t));
  T value;
  type_holder #(T) holder;
endclass

// A typedef to another specialization of the base leaves inherited T alone.
class other_spec extends value_base #(6);
  typedef value_base #(5) other_t;
  typedef T local_t;
  T value;
  type_holder #(local_t) holder;
endclass

typedef class static_owner;

// Names in another class's declarations resolve in that class.
class static_reader extends value_base #(9);
  type_holder #(static_owner::owner_t) holder;
  static function int owner_bits();
    return $bits(static_owner::value);
  endfunction
endclass

class local_reader extends local_base #(9);
  type_holder #(static_owner::owner_t) holder;
  static function int owner_bits();
    return $bits(static_owner::value);
  endfunction
endclass

class static_owner extends value_base #(5);
  typedef T owner_t;
  static T value;
endclass

typedef bit [10:0] unit_t;

class default_holder #(
    type P = type_holder #(unit_t)
);
  P holder;
endclass

module scope_probe #(
    int N = 1
) (
    output bit [N-1:0] value
);
  assign value = '1;
endmodule

module type_probe #(
    type T = int
) (
    output T value
);
  assign value = '1;
endmodule

module t;
  bit [14:0] module_value;
  unit_t type_value;
  scope_probe #(15) probe (module_value);
  type_probe #(unit_t) type_probe_i (type_value);
  scoped_value scoped;
  packed_range packed_bits;
  bits_query queried_bits;
  type_query queried_type;
  type_query #(65) wide_type;
  other_spec other;
  static_reader reader;
  local_reader local_reader_obj;
  default_holder #(type_holder #(bit [2:0])) overridden;
  initial begin
    scoped = new;
    scoped.holder = new;
    packed_bits = new;
    queried_bits = new;
    queried_type = new;
    queried_type.holder = new;
    wide_type = new;
    wide_type.holder = new;
    other = new;
    other.holder = new;
    reader = new;
    reader.holder = new;
    local_reader_obj = new;
    local_reader_obj.holder = new;
    overridden = new;
    overridden.holder = new;
    `checkd($bits(scoped.value), 7);
    `checkd($bits(scoped.holder.value), 7);
    `checkd($bits(packed_bits.value), 15);
    `checkd($bits(queried_bits.value), 31);
    `checkd($bits(queried_type.value), 33);
    `checkd($bits(queried_type.holder.value), 33);
    `checkd($bits(wide_type.value), 65);
    `checkd($bits(wide_type.holder.value), 65);
    `checkd($bits(other.value), 6);
    `checkd($bits(other.holder.value), 6);
    `checkd(static_reader::owner_bits(), 5);
    `checkd($bits(reader.holder.value), 5);
    `checkd(local_reader::owner_bits(), 5);
    `checkd($bits(local_reader_obj.holder.value), 5);
    `checkd($bits(module_value), 15);
    `checkd($bits(type_value), 11);
    `checkd($bits(overridden.holder.value), 3);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
