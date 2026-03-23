// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 jalcim
// SPDX-License-Identifier: CC0-1.0

// Recursive constant function defined at file scope ($unit).
// Without the V3Scope.cpp fix, this triggers:
//   %Error: Internal Error: V3Scope.cpp: No clone for package function

function automatic integer gate_depth;
  input integer way;
  integer d1, d2, sc, n1, n2;
  begin
    if (way <= 1) gate_depth = 0;
    else if (way <= 4) gate_depth = 1;
    else begin
      sc = $clog2(way);
      n1 = 1 << (sc - 1);
      n2 = way - n1;
      d1 = gate_depth(n1);
      d2 = gate_depth(n2);
      gate_depth = ((d1 > d2) ? d1 : d2) + 1;
    end
  end
endfunction

module t;
  localparam D5 = gate_depth(5);
  localparam D8 = gate_depth(8);

  initial begin
    if (D5 !== 2) $stop;
    if (D8 !== 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
