// DESCRIPTION: Verilator: Self-checking test for localparams inside loop generate blocks

module t;
   for (genvar i = 0; i < 2; i++) begin : g
      localparam int DEP = 10 + i;
   end
   initial begin
      if (g.DEP != 10) $stop;
      if (g.DEP != 11) $stop;
      $write("*-* All Covered *-*\n");
      $finish;
   end
endmodule
