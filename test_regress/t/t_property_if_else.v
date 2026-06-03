// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  int vacuous_passes = 0;

  wire sel = cyc inside {2, 6};
  wire a = sel;
  wire b = (cyc == 3) || (cyc == 7);
  wire c = !sel;
  wire nested_outer = cyc inside {2, 4, 6};
  wire nested_inner = cyc inside {2, 6};

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      `checkd(vacuous_passes, 10);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  property p_named;
    if (sel) a else c;
  endproperty

  // One-arm property if: false condition is a vacuous pass.
  assert property (@(posedge clk) if (sel) a) begin
    if (cyc != 0) ++vacuous_passes;
  end else
    $stop;

  // Branch selection: untaken branch must not affect result.
  assert property (@(posedge clk) if (sel) 1'b1 else c)
  else $stop;
  assert property (@(posedge clk) if (!sel) c else 1'b1)
  else $stop;

  // Named property body.
  assert property (@(posedge clk) p_named)
  else $stop;

  // Temporal branch: if sel is true, require b on the following cycle; otherwise
  // the else branch is checked on the current cycle.
  assert property (@(posedge clk) if (sel) a |-> ##1 b else c)
  else $stop;

  // Dangling else binds to the inner property if. If it bound to the outer if,
  // the false outer condition would select the failing 1'b0 branch.
  assert property (@(posedge clk) if (nested_inner) if (nested_inner) 1'b1 else 1'b0)
  else $stop;

  // Fully nested if/else: checks the inner else at cyc == 4, the inner then at
  // cyc == 2/6, and the outer else on all other cycles.
  assert property (@(posedge clk)
                   if (nested_outer) if (nested_inner) 1'b1 else !nested_inner
                   else !nested_outer)
  else $stop;

endmodule
