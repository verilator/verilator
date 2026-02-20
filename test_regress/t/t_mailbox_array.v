// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
   localparam DWIDTH = 6;
   typedef int my_type_t [2**DWIDTH];
   mailbox #(my_type_t) m_mbx;

   function new();
      this.m_mbx = new(1);
   endfunction
endclass

module tb_top();
   Cls c;
   initial begin
      c = new();
      $display("%p", c);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
