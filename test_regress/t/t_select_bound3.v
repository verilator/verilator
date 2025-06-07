// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

class cls;
   int m_field;
endclass

module t();
   cls inst[2];

   initial begin
      // Loop (even just 1 iteration) is needed to reproduce the error
      for (int i = 0; i < 2; ++i) begin
         inst[i] = new();
         inst[i].m_field = i;
      end
      for (int i = 0; i < 2; ++i) begin
         if (inst[i].m_field != i) $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
    end
endmodule
