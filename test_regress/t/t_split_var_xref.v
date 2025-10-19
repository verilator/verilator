// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro
// SPDX-License-Identifier: CC0-1.0

module child (
    input logic test_out
);
  initial begin
    #1;
    if (test_out != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module parent;
  logic [1:0] test_out;

  child u0 (.test_out(test_out[0]));
endmodule

interface my_if;
  initial begin
    t.test_parent.test_out = 1;
  end
endinterface

module t;
  parent test_parent ();
  my_if intf ();
endmodule
