// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) \
  do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0)
// verilog_format: on

module t;
  bit virtual_deep_after;
  bit after_super;
  process ctor_victim;
  process virtual_victim;
  process super_victim;

  class base_killer;
    virtual function automatic void kill_virtual(process p);
    endfunction
  endclass

  class derived_killer extends base_killer;
    function new();
      ctor_victim.kill();
    endfunction
    function automatic void kill_virtual(process p);
      p.kill();
      virtual_deep_after = 1'b1;
    endfunction
  endclass

  class base_constructor_killer;
    function new(process victim);
      victim.kill();
    endfunction
  endclass

  class derived_constructor_killer extends base_constructor_killer;
    function new(process victim);
      super.new(victim);
      after_super = 1'b1;
    endfunction
  endclass

  initial begin
    automatic derived_killer derived;
    automatic base_killer polymorphic;
    automatic derived_constructor_killer super_killer;
    fork
      begin
        ctor_victim = process::self();
        #10;
      end
      begin
        virtual_victim = process::self();
        #10;
      end
      begin
        super_victim = process::self();
        #10;
      end
    join_none
    #1;
    derived = new;  // Derived constructor kills, base constructor does not
    polymorphic = derived;
    polymorphic.kill_virtual(virtual_victim);  // Kills another process, caller continues
    super_killer = new(super_victim);
    `checkd(ctor_victim.status(), process::KILLED);
    `checkd(virtual_victim.status(), process::KILLED);
    `checkd(virtual_deep_after, 1'b1);
    `checkd(super_victim.status(), process::KILLED);
    `checkd(after_super, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
