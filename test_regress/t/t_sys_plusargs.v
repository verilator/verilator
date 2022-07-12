// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   integer p_i;     // signal type IData
   reg [15:0] p_s;  // signal type SData
   reg [7:0] p_c;   // signal type CData
   real p_r;        // signal type double
   reg [7*8:1] p_str;
   string      sv_str;
   reg [7*8:1] p_in;
   string      sv_in;

   initial begin
      if ($test$plusargs("PLUS")!==1) $stop;
      if ($test$plusargs("PLUSNOT")!==0) $stop;
      if ($test$plusargs("PL")!==1) $stop;
      //if ($test$plusargs("")!==1) $stop;  // Simulators differ in this answer
      if ($test$plusargs("NOTTHERE")!==0) $stop;

      sv_in = "PLUS";
`ifdef VERILATOR
      if ($c1(0)) sv_in = "NEVER"; // Prevent constant propagation
`endif
      if ($test$plusargs(sv_in)!==1) $stop;

      p_i = 10;
      if ($value$plusargs("NOTTHERE%d", p_i) !== 0) $stop;
      if ($value$plusargs("NOTTHERE%0d", p_i) !== 0) $stop;
      if (p_i !== 10) $stop;

      p_i = 0;
      if ($value$plusargs("INT=%d", p_i) !== 1) $stop;
      if (p_i !== 32'd1234) $stop;

      p_i = 0;
      if ($value$plusargs("INT=%0d", p_i) !== 1) $stop;
      if (p_i !== 32'd1234) $stop;

      p_i = 0;
      if ($value$plusargs("INT=%H", p_i)!==1) $stop;  // tests uppercase % also
      if (p_i !== 32'h1234) $stop;

      p_i = 0;
      // Check octal and WIDTH
      if (!$value$plusargs("INT=%o", p_i)) $stop;
      if (p_i !== 32'o1234) $stop;

      // Check handling of 'SData' type signals (Issue #1592)
      p_s = 0;
      if (!$value$plusargs("INT=%d", p_s)) $stop;
      if (p_s !== 16'd1234) $stop;

      // Check handling of 'CData' type signals (Issue #1592)
      p_c = 0;
      if (!$value$plusargs("INT=%d", p_c)) $stop;
      if (p_c !== 8'd210) $stop;

      // Check handling of 'double' type signals (Issue #1619)
      p_r = 0;
      if (!$value$plusargs("REAL=%e", p_r)) $stop;
      $display("r='%e'", p_r);
      if (p_r !== 1.2345) $stop;

      p_r = 0;
      if (!$value$plusargs("REAL=%f", p_r)) $stop;
      $display("r='%f'", p_r);
      if (p_r !== 1.2345) $stop;

      p_r = 0;
      if (!$value$plusargs("REAL=%g", p_r)) $stop;
      $display("r='%g'", p_r);
      if (p_r !== 1.2345) $stop;

      p_str = "none";
      if ($value$plusargs("IN%s", p_str)!==1) $stop;
      $display("str='%s'",p_str);
      if (p_str !== "T=1234") $stop;

      sv_str = "none";
      if ($value$plusargs("IN%s", sv_str)!==1) $stop;
      $display("str='%s'",sv_str);
      if (sv_str != "T=1234") $stop;

      sv_str = "none";
      $value$plusargs("IN%s", sv_str);
      $display("str='%s'",sv_str);
      if (sv_str != "T=1234") $stop;

      p_in = "IN%s";
`ifdef VERILATOR
      p_in = $c(p_in); // Prevent constant propagation
`endif
      sv_str = "none";
      if ($value$plusargs(p_in, sv_str)!==1) $stop;
      $display("str='%s'",sv_str);
      if (sv_str != "T=1234") $stop;

      sv_str = "none";
      if ($value$plusargs("IP%%P%b", p_i)!==1) $stop;
      $display("str='%s'",sv_str);
      if (p_i != 'b101) $stop;

      sv_in = "INT=%d";
`ifdef VERILATOR
      if ($c1(0)) sv_in = "NEVER"; // Prevent constant propagation
`endif
      p_i = 0;
      if ($value$plusargs(sv_in, p_i)!==1) $stop;
      $display("i='%d'",p_i);
      if (p_i !== 32'd1234) $stop;

      // bug3131 - really "if" side effect test
      p_i = 0;
      if ($value$plusargs("INT=%d", p_i)) ;
      if (p_i !== 32'd1234) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
