// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class RandomValue;
  rand int value;
  constraint small_int_c {value < 10;}
  task disable_val();
    value.rand_mode(0);
  endtask
endclass

class Base;
  rand RandomValue v = new;
endclass

class Foo extends Base;
endclass

package uvm_pkg;
  virtual class uvm_object;
  endclass

  class uvm_sequence_item;
  endclass

  virtual class uvm_sequencer_param_base;
    function void send_request(uvm_sequence_item t);
      uvm_sequence_item par;
      if (0 == par.randomize()) begin
      end
    endfunction
  endclass

  class uvm_reg_item extends uvm_sequence_item;
    rand uvm_object extension;
  endclass

  class uvm_reg_field extends uvm_object;
    rand int value;
    virtual function bit get_rand_mode();
      return bit'(value.rand_mode());
    endfunction
  endclass

endpackage

module t_constraint_global_randMode;
  import uvm_pkg::*;

  class reg_r extends uvm_object;
    rand int value;
    local rand uvm_reg_field _dummy;
    constraint _dummy_is_reg {_dummy.value == value;}
    function new();
      _dummy = new;
    endfunction
  endclass

  initial begin
    Foo d;
    Base b;
    reg_r r;

    // Test 1: Member class with randmode
    d = new;
    b = d;
    b.v.disable_val();
    b.v.value = 11;
    /* verilator lint_off WIDTHTRUNC */
    if (bit'(b.randomize())) $stop;
    if (b.v.value != 11) $stop;

    // Test 2: Member class without randmode
    r = new;
    if (!r.randomize()) $stop;
    /* verilator lint_on WIDTHTRUNC */

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
