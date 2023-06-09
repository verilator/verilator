module verilator_latch
(
   input  logic        state,
   output logic [31:0] b
);

   function logic [31:0 ] toto ();
      logic [31:0] res;
      res = 10;
      return res;
   endfunction

   always_comb
   begin
      b = 0;
      if (state)
          b = toto();
   end

endmodule;
