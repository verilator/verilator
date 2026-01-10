// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Cls;
  task take_ref(ref logic s);
  endtask
endclass

module t;
  logic a;
  logic b = 1;
  Cls cls = new;

  initial begin
    force a = b;
    cls.take_ref(a);
    cls.take_ref(b);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
