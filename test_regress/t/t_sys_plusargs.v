// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t;

   integer p_i;
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

      p_i = 10;
      if ($value$plusargs("NOTTHERE%d", p_i)!==0) $stop;
      if (p_i !== 10) $stop;

      p_i = 0;
      if ($value$plusargs("INT=%d", p_i)!==1) $stop;
      if (p_i !== 32'd1234) $stop;

      p_i = 0;
      if ($value$plusargs("INT=%H", p_i)!==1) $stop;  // tests uppercase % also
      if (p_i !== 32'h1234) $stop;

      p_i = 0;
      // Check octal and WIDTH
      if (!$value$plusargs("INT=%o", p_i)) $stop;
      if (p_i !== 32'o1234) $stop;

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

      sv_in = "INT=%d";
`ifdef VERILATOR
      if ($c1(0)) sv_in = "NEVER"; // Prevent constant propagation
`endif
      p_i = 0;
      if ($value$plusargs(sv_in, p_i)!==1) $stop;
      $display("i='%d'",p_i);
      if (p_i !== 32'd1234) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
