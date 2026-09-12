// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Tests look for magic string "Dead" not to exist; V3Dead should remove these

class ABase;
  function void meth_Dead;  // Never used
  endfunction
  virtual function int virt_Dead;  // Never used
    return 0;
  endfunction
  virtual function int virt_demote;  // Only in base, demoted
    return 42;
  endfunction
  virtual function int virt_keep;
    return 0;
  endfunction
endclass

class AInh1 extends ABase;
  virtual function int virt_Dead;  // Never used
    return 1;
  endfunction
  virtual function int virt_keep;
    return 1;
  endfunction
endclass

class AInh2 extends ABase;
  virtual function int virt_Dead;  // Never used
    return 2;
  endfunction
  virtual function int virt_keep;
    return 2;
  endfunction
endclass

class ADead extends ABase;  // TODO not yet removed
endclass

module t;
  function void mod_func_Dead;  // Never used
  endfunction
  initial begin
    ABase i1;
    ABase i2;
    i1 = AInh1::new;
    i2 = AInh2::new;
    `checkd(i1.virt_demote(), 42);
    `checkd(i2.virt_demote(), 42);
    `checkd(i1.virt_keep(), 1);
    `checkd(i2.virt_keep(), 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
