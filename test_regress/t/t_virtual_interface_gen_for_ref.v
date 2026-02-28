// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

package uvm_pkg;
  class uvm_resource_db #(
      type T = int
  );
    static T interf;

    static function void set(input T accessor);
      interf = accessor;
    endfunction
  endclass

  class uvm_config_db #(
      type T = int
  ) extends uvm_resource_db #(T);
  endclass
endpackage


interface iface ();
  int x = 1;
endinterface

module t;
  import uvm_pkg::*;

  bind bound iface if_bind ();
  dut i_dut ();

  initial begin
    uvm_config_db#(virtual iface)::set(
        t.i_dut.first_gen[0].i_fail.i_a.i_b.i_c.second_gen[0].i_d.i_bound.if_bind);

    if (uvm_config_db#(virtual iface)::interf.x != 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module bound ();
endmodule

module dut ();
  genvar g_core;
  generate
    for (g_core = 0; g_core < 1; g_core++) begin : first_gen
      fail_mod i_fail ();
    end
  endgenerate
endmodule

module fail_mod ();
  a i_a ();
endmodule

module a ();
  b i_b ();
endmodule
;

module b ();
  c i_c ();
endmodule

module c ();
  genvar gi;
  generate
    for (gi = 0; gi < 1; gi++) begin : second_gen
      d i_d ();
    end
  endgenerate
endmodule

module d ();
  bound i_bound ();
endmodule
