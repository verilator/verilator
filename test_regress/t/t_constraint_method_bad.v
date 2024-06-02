// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int m_one;

   constraint cons { m_one > 0 && m_one < 2; }

   task test1;
      cons.bad_method(1);  // BAD
   endtask

endclass

module t (/*AUTOARG*/);
endmodule
