// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  // dist
  class Cls;
    rand bit dict[int unsigned];
    function void call_rand;
      void'(randomize() with {
        dict[0] dist {
          1 :/ 1
        };
      });
    endfunction
  endclass

  // foreach
  int dict1d[int];
  int dict2d[int][string];
  int dict3d[int][string][int];
  Cls cls;
  initial begin
    // 1D
    foreach (dict1d[b]) begin
      $error(b);  // should never reach
    end
    `checkd(dict1d.size(), 0);

    // 2D
    foreach (dict2d[0][b]) begin
      $error(b);  // should never reach
    end
    `checkd(dict2d.size(), 0);

    // 3D
    foreach (dict3d[0][i]) begin
      foreach (dict3d[0][i][j]) begin
        $error(i, j);  // should never reach
      end
    end
    `checkd(dict3d.size(), 0);

    cls = new;
    cls.call_rand();
    `checkd(cls.dict.size(), 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
