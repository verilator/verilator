// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Tests look for magic string "Dead" not to exist; V3Dead should remove these

class BaseClass_Dead;
endclass

class EmptyClass_Dead extends BaseClass_Dead;
endclass

package Pack_Dead;
  typedef bit typedef_Dead;
endpackage

module Mod_Dead;
  typedef class ModClass_Co_Dead;
  class ModClass_Dead;
    int m_b_Dead;
    ModClass_Co_Dead m_co_dead;
    task method_Dead;
    endtask
    static task method_static_Dead;
    endtask
  endclass
  class ModClass_Co_Dead;
    ModClass_Dead m_dead;  // Check that ModClass_Dead<->ModClass_Co_Dead link gets Deadified
  endclass
endmodule

module Mod_Empty_Dead;
endmodule

module Mod_Parent_Empty_Dead;
  Mod_Empty_Dead sub ();
endmodule

interface If_Dead;
  function void if_func_Dead;
  endfunction
  modport modport_Dead(import if_func_Dead);
endinterface

package Pkg_public_kpt;
  parameter int public_int_Keep  /*verilator public_flat_rd*/ = 5;
endpackage

package Pkg_Keep;
  import "DPI-C" function void dpii_Keep();

  export "DPI-C" function dpix_Keep;
  function void dpix_Keep;
  endfunction
endpackage

module t (  /*AUTOARG*/);

  typedef struct {int struct_member_Dead;} struct_Dead_t;
  struct_Dead_t var_struct_Dead;

  typedef int typedef_Dead1_t;
  typedef typedef_Dead1_t typedef_Dead2_t;

  function void func_Dead;
  endfunction

  generate
    if (0) begin
      Mod_Dead cell_nogen_Dead ();
      If_Dead if_nogen_Dead ();
    end
  endgenerate

  Mod_Empty_Dead cell_empty_Dead ();
  Mod_Parent_Empty_Dead cell_parent_empty_Dead ();

  typedef_Dead1_t assigned_to_Dead1;
  typedef_Dead2_t assigned_to_Dead2;
  typedef_Dead2_t assigned_to_Dead3;
  typedef_Dead2_t assigned_to_Dead4;
  typedef_Dead2_t assigned_to_Dead5;
  typedef_Dead2_t assigned_to_Dead6;

  always_comb assigned_to_Dead6 = assigned_to_Dead5;
  always_comb assigned_to_Dead5 = assigned_to_Dead4;
  always_comb assigned_to_Dead4 = assigned_to_Dead3;
  always_comb assigned_to_Dead3 = assigned_to_Dead2;
  always_comb assigned_to_Dead2 = assigned_to_Dead1;

  initial begin
    assigned_to_Dead1 = 1;
    assigned_to_Dead1 = 2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
