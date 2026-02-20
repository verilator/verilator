// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   initial begin
      fork : foo
         disable foo;
         #1 $stop;
      join_none
      #2;
      begin : forked
         fork
            disable forked;
            #1 $stop;
         join_none
      end
      #2;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
