// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/
   clk
);
  input clk;

  int cycles = 0;
  always @(posedge clk) begin
    cycles <= cycles + 1;
    begin
      int z, w;
      z = cycles + 7;
      for (int f = 0; f < 2; ++f) begin
        for (int e = 0; e < 2; ++e) begin
          w = z;
          // The first read precedes the assignment of 5, even after nested unrolling.
          if (f == 0 && e == 0) begin
            `checkd(w, cycles + 7);
          end else begin
            `checkd(w, 5);
          end
          z = 5;
        end
      end
    end
    if (cycles == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
