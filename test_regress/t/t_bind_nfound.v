// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface bound_if;
endinterface

module t;

  sub sub ();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module sub_ext;
  // verilator lint_off MODMISSING
  bind sub_inst bound_if i_bound ();
  // verilator lint_on MODMISSING
endmodule

module sub;
  sub_ext sub_ext ();
endmodule
