// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.

module foo
  #( parameter type bar = logic)
   (output int bar_size);

   localparam baz = $bits(bar);

   assign bar_size = baz;
endmodule

module t();
   logic [7:0] qux1;
   int bar_size1;

   foo #(.bar (logic [ $bits(qux1) - 1 : 0]))
   foo_inst1 (.bar_size (bar_size1));

   logic [7:0] qux2;
   int bar_size2;

   foo #(.bar (logic [ $bits(qux2) - 1 : 0]))
   foo_inst2 (.bar_size (bar_size2));

   logic [7:0] qux3;
   int bar_size3;

   foo #(.bar (logic [ $bits(qux3) - 1 : 0]))
   foo_inst3 (.bar_size (bar_size3));

   initial begin
//       if ($bits(qux) != $bits(foo_inst.baz)) begin
//          $display("%m: bits of qux != bits of foo_inst.baz (%0d, %0d)",
//                   $bits(qux), $bits(foo_inst.baz));
//          $stop();
//       end
      if (bar_size1 != $bits(qux1)) begin
         $display("%m: bar_size1 != bits of qux1 (%0d, %0d)",
                 bar_size1, $bits(qux1));
         $stop();
      end
      if (bar_size2 != $bits(qux2)) begin
         $display("%m: bar_size2 != bits of qux2 (%0d, %0d)",
                 bar_size2, $bits(qux2));
         $stop();
      end
      if (bar_size3 != $bits(qux3)) begin
         $display("%m: bar_size3 != bits of qux3 (%0d, %0d)",
                 bar_size3, $bits(qux3));
         $stop();
      end
   end

   genvar m;
   generate
      for (m = 1; m <= 8; m+=1) begin : gen_m
//            initial begin
//                if (m != $bits(foo_inst.baz)) begin
//                   $display("%m: m != bits of foo_inst.baz (%0d, %0d)",
//                            m, $bits(foo_inst.baz));
//                   $stop();
//                end
//            end

            foo #(.bar (logic[m-1:0])) foo_inst (.bar_size ());
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
