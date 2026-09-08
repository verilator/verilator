// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

class scoped_types #(
    int N = 1
);
  typedef logic [N-1:0] FIRST_T;
endclass
class type_pair #(
    type FIRST_T = int,
    type SECOND_T = int
);
  typedef FIRST_T first_t;
  FIRST_T first;
  SECOND_T second;
endclass
class type_base #(
    type FIRST_T = int,
    type SECOND_T = FIRST_T
);
  typedef FIRST_T base_t;
endclass

class item;
  int value;
endclass
class positional_derived extends type_base #(item);
  type_pair #(FIRST_T, SECOND_T) inherited_pair;
  type_pair #(scoped_types #(15)::FIRST_T, SECOND_T) scoped_pair;
endclass
class named_derived extends type_base #(
    .SECOND_T(logic [14:0]),
    .FIRST_T(logic [6:0])
);
  type_pair #(
      .SECOND_T(SECOND_T),
      .FIRST_T(FIRST_T)
  ) inherited_pair;
endclass
class grand_derived extends named_derived;
  type_pair #(base_t, SECOND_T) typedef_pair;
endclass
class typedef_derived extends type_base #(logic [32:0]);
  typedef FIRST_T local_t;
  typedef type (1 + 2) type_op_t;
  type_op_t type_op_value;
  base_t base_value;
  named_derived::base_t named_value;
  scoped_types #(15)::FIRST_T scoped_value;
  type_pair #(local_t, SECOND_T) inherited_pair;
endclass
class default_middle #(
    int N = 1
) extends type_base;
endclass
class default_derived extends default_middle #(7);
  type_pair #(FIRST_T, SECOND_T) inherited_pair;
endclass
class param_derived #(
    type T = int
) extends type_base #(T);
  type_pair #(FIRST_T, SECOND_T) inherited_pair;
endclass
class chained_base #(
    int N = 1
) extends type_base #(logic [N-1:0]);
  typedef FIRST_T chained_t;
endclass
class chained_derived extends chained_base #(13);
  type_pair #(chained_t) chained_pair;
endclass
class scoped_derived extends type_base #(logic [18:0]);
  typedef type_pair #(FIRST_T)::first_t first_t;
  first_t scoped_first;
endclass
class struct_derived extends type_base #(logic [22:0]);
  typedef type_pair #(struct packed {FIRST_T value;}) struct_pair_t;
  struct_pair_t struct_pair;
endclass
class alias_derived extends type_base #(logic [2:0]);
  typedef scoped_types #(21) scoped21_t;
  type_pair #(struct packed {scoped21_t::FIRST_T value;}) alias_pair;
endclass
class qualified_user;
  type_pair #(chained_base #(17)::base_t, type_base #(logic [10:0])::FIRST_T) qualified_pair;
endclass
class value_base #(
    int N = 2
);
  protected typedef logic [N-1:0] protected_t;
  local typedef logic [N:0] private_t;
  type_pair #(private_t) private_pair;
endclass
class value_holder #(
    int N = 3
);
  function int get();
    return N;
  endfunction
endclass
class value_derived extends value_base #(42);
  value_holder #(N + 1) holder;
  protected_t protected_value;
  type_pair #(protected_t, type(protected_t)) protected_pair;
  type_pair #(struct packed { protected_t value; }) struct_pair;
endclass

module t;
  positional_derived positional;
  named_derived named;
  grand_derived grand;
  typedef_derived typedefs;
  default_derived defaults;
  param_derived #(logic [30:0]) param31;
  param_derived #(logic [64:0]) param65;
  chained_derived chained;
  scoped_derived scoped;
  struct_derived structs;
  alias_derived aliases;
  value_derived values;
  qualified_user qualified;
  initial begin
    positional = new;
    positional.inherited_pair = new;
    positional.inherited_pair.first = new;
    positional.inherited_pair.second = positional.inherited_pair.first;
    positional.scoped_pair = new;
    positional.scoped_pair.second = positional.inherited_pair.first;
    `checkd($bits(positional.scoped_pair.first), 15);
    for (int i = 0; i < 4; ++i) begin
      positional.inherited_pair.first.value = i;
      `checkd(positional.inherited_pair.second.value, i);
      `checkd(positional.scoped_pair.second.value, i);
    end
    named = new;
    named.inherited_pair = new;
    `checkd($bits(named.inherited_pair.first), 7);
    `checkd($bits(named.inherited_pair.second), 15);
    grand = new;
    grand.typedef_pair = new;
    `checkd($bits(grand.typedef_pair.first), 7);
    `checkd($bits(grand.typedef_pair.second), 15);
    typedefs = new;
    typedefs.inherited_pair = new;
    `checkd($bits(typedefs.inherited_pair.first), 33);
    `checkd($bits(typedefs.inherited_pair.second), 33);
    `checkd($bits(typedefs.type_op_value), 32);
    `checkd($bits(typedefs.base_value), 33);
    `checkd($bits(typedefs.named_value), 7);
    `checkd($bits(typedefs.scoped_value), 15);
    defaults = new;
    defaults.inherited_pair = new;
    `checkd($bits(defaults.inherited_pair.first), 32);
    `checkd($bits(defaults.inherited_pair.second), 32);
    param31 = new;
    param31.inherited_pair = new;
    `checkd($bits(param31.inherited_pair.first), 31);
    `checkd($bits(param31.inherited_pair.second), 31);
    param65 = new;
    param65.inherited_pair = new;
    `checkd($bits(param65.inherited_pair.first), 65);
    `checkd($bits(param65.inherited_pair.second), 65);
    chained = new;
    chained.chained_pair = new;
    `checkd($bits(chained.chained_pair.first), 13);
    scoped = new;
    `checkd($bits(scoped.scoped_first), 19);
    structs = new;
    structs.struct_pair = new;
    `checkd($bits(structs.struct_pair.first.value), 23);
    aliases = new;
    aliases.alias_pair = new;
    `checkd($bits(aliases.alias_pair.first.value), 21);
    qualified = new;
    qualified.qualified_pair = new;
    `checkd($bits(qualified.qualified_pair.first), 17);
    `checkd($bits(qualified.qualified_pair.second), 11);
    values = new;
    values.holder = new;
    `checkd(values.holder.get(), 43);
    values.private_pair = new;
    `checkd($bits(values.private_pair.first), 43);
    values.protected_pair = new;
    `checkd($bits(values.protected_value), 42);
    `checkd($bits(values.protected_pair.first), 42);
    `checkd($bits(values.protected_pair.second), 42);
    values.struct_pair = new;
    `checkd($bits(values.struct_pair.first.value), 42);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
