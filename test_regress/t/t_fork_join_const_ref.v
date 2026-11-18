// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Reader;
  task check(const ref logic [63:0] words[], const ref byte flags[$], ref int updates);
    fork
      begin
        #2;
        if (words.size() != 2 || words[1] != 64'h12345678_abcdef01) $stop;
        if (flags.size() != 2 || flags[1] != 17) $stop;
        updates += int'(flags[1]);
      end
      begin
        #1;
        ++updates;
      end
    join
  endtask
endclass

module t;
  initial begin
    Reader r;
    logic [63:0] words[];
    byte flags[$];
    int updates;
    r = new;
    words = '{64'd3, 64'd5};
    flags = '{3};
    updates = 4;
    fork
      r.check(words, flags, updates);
      begin
        #1;
        words[1] = 64'h12345678_abcdef01;
        flags.push_back(17);
      end
    join
    if (updates != 22 || $time != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
