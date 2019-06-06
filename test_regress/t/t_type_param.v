// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.

module foo
  #( parameter type bar = logic)
   ();

   localparam baz = $bits(bar);
endmodule

module t();
   logic [7:0] qux;

   foo #(.bar (logic [ $bits(qux) - 1 : 0])) foo_inst ();
//   initial begin
//       if ($bits(qux) != $bits(foo_inst.baz)) begin
//          $display("%m: m != bits of foo_inst.baz (%0d, %0d)",
//                   $bits(qux), $bits(foo_inst.baz));
//          $stop();
//       end
//   end

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

            foo #(.bar (logic[m-1:0])) foo_inst ();
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
