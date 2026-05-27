// DESCRIPTION: Verilator: Verilog Test module
//
// Reference to a parameterized-class typedef (r#(1)::t) buried inside a
// unit-scope struct typedef, passed as an interface type-parameter value.
// Exercises resolveParamClassRefDType's recursion into struct/union members.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class r #(parameter int W = 1);
  typedef struct packed { logic [W-1:0] unused; } t;
endclass

typedef struct packed { r#(1)::t f; } tf;

interface ifc #(parameter type T = logic);
endinterface

module t;
  ifc #(.T(tf)) bad ();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
