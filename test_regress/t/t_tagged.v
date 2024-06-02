// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   typedef union tagged {
     void m_invalid;
     int m_int;
   } u_t;

   u_t u;
   string s;

   initial begin
      u = tagged m_invalid;
      s = $sformatf("%p", u);
      $display("%s e.g. '{tagged m_invalid:void}", s);
      case (u) matches
        tagged m_invalid: ;
        tagged m_int: $stop;
        default: $stop;
      endcase
      if (u matches tagged m_invalid) ;
      if (u matches tagged m_int .n) $stop;

      u = tagged m_int (123);
      s = $sformatf("%p", u);
      $display("'%s e.g. '{tagged m_int:123}", s);
      case (u) matches
        tagged m_invalid: $stop;
        tagged m_int .n: if (n !== 123) $stop;
        default: $stop;
      endcase
      if (u matches tagged m_invalid) $stop;
      if (u matches tagged m_int .n) if (n != 123) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
