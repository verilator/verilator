// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t;
   //  verilator lint_off PINMISSING
`ifdef T_GEN_MISSING_BAD
   foobar #(.FOO_TYPE(1)) foobar;  // This means we should instatiate missing module
`elsif T_GEN_MISSING
   foobar #(.FOO_TYPE(0)) foobar;  // This means we should instatiate foo0
`else
 `error "Bad Test"
`endif
endmodule


module foobar
  #( parameter
     FOO_START = 0,
     FOO_NUM = 2,
     FOO_TYPE = 1
     )
    (
    input wire[FOO_NUM-1:0] foo, 
    output wire[FOO_NUM-1:0] bar);


   generate
      begin: g
         genvar j;
         for (j = FOO_START; j < FOO_NUM+FOO_START; j = j + 1)
           begin: foo_inst;
              if (FOO_TYPE == 0)
                begin: foo_0
                   // instatiate foo0
                   foo0 i_foo(.x(foo[j]), .y(bar[j]));
                end
              if (FOO_TYPE == 1)
                begin: foo_1
                   // instatiate foo1
                   foo_not_needed i_foo(.x(foo[j]), .y(bar[j]));
                end
           end
      end
   endgenerate
endmodule



module foo0(input wire x, output wire y);

   assign y = ~x;
   
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
