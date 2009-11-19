// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t;

   integer p_i;
   reg [7*8:1] p_str;

   initial begin
      if ($test$plusargs("PLUS")!==1) $stop;
      if ($test$plusargs("PLUSNOT")!==0) $stop;
      if ($test$plusargs("PL")!==1) $stop;
      //if ($test$plusargs("")!==1) $stop;  // Simulators differ in this answer
      if ($test$plusargs("NOTTHERE")!==0) $stop;

      p_i = 10;
      if ($value$plusargs("NOTTHERE%d", p_i)!==0) $stop;
      if (p_i !== 10) $stop;

      if ($value$plusargs("INT=%d", p_i)!==1) $stop;
      if (p_i !== 32'd1234) $stop;

      if ($value$plusargs("INT=%H", p_i)!==1) $stop;  // tests uppercase % also
      if (p_i !== 32'h1234) $stop;

      if ($value$plusargs("INT=%o", p_i)!==1) $stop;
      if (p_i !== 32'o1234) $stop;

      if ($value$plusargs("IN%s", p_str)!==1) $stop;
      $display("str='%s'",p_str);
      if (p_str !== "T=1234") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
