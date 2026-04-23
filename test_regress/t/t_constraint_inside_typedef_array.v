// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  typedef int int_q[$];
  typedef int int_da[];
  typedef int int_up[4];
  typedef int_q alias_q;

  class Bundle;
    int_q  q;
    int_da d;
    int_up u;
  endclass
endpackage

module t(/*AUTOARG*/);
  import pkg::*;

  initial begin
    automatic Bundle b = new();
    automatic int    t_l = 0;
    automatic int    rv;
    automatic alias_q a = '{32'd1, 32'd2, 32'd3};

    b.q = '{32'd10, 32'd20, 32'd30};
    b.d = new[3];
    b.d = '{32'd40, 32'd50, 32'd60};
    b.u = '{32'd70, 32'd80, 32'd90, 32'd100};

    // Original reported shape: typedef queue member of a class,
    // used as the array in `inside {...}` of a with-constraint.
    repeat (20) begin
      rv = std::randomize(t_l) with { t_l inside {b.q}; };
      `checkd(rv, 1);
      `checkd((t_l == 10 || t_l == 20 || t_l == 30), 1'b1);
    end

    // Typedef dynamic array.
    repeat (20) begin
      rv = std::randomize(t_l) with { t_l inside {b.d}; };
      `checkd(rv, 1);
      `checkd((t_l == 40 || t_l == 50 || t_l == 60), 1'b1);
    end

    // Typedef unpacked (fixed-size) array.
    repeat (20) begin
      rv = std::randomize(t_l) with { t_l inside {b.u}; };
      `checkd(rv, 1);
      `checkd((t_l == 70 || t_l == 80 || t_l == 90 || t_l == 100), 1'b1);
    end

    // Chained typedef (AstRefDType -> AstRefDType -> QueueDType) must
    // also be unwrapped by skipRefp().
    repeat (20) begin
      rv = std::randomize(t_l) with { t_l inside {a}; };
      `checkd(rv, 1);
      `checkd((t_l == 1 || t_l == 2 || t_l == 3), 1'b1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
