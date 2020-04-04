// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module foo
  #(parameter type bar = logic)
   (output int bar_size);

   localparam baz = $bits(bar);

   assign bar_size = baz;
endmodule

module foo_wrapper
  #(parameter bar_bits = 9)
   (output int bar_size);

   foo #(.bar (logic[bar_bits-1:0])) foo_inst (.bar_size (bar_size));

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

   localparam bar_bits = 13;
   int bar_size_wrapper;

   foo_wrapper #(.bar_bits (bar_bits))
   foo_wrapper_inst (.bar_size (bar_size_wrapper));

   initial begin
       if ($bits(qux1) != foo_inst1.baz) begin
          $display("%m: bits of qux1 != bits of foo_inst1.baz (%0d, %0d)",
                   $bits(qux1), foo_inst1.baz);
          $stop();
       end
       if ($bits(qux2) != foo_inst2.baz) begin
          $display("%m: bits of qux2 != bits of foo_inst2.baz (%0d, %0d)",
                   $bits(qux2), foo_inst2.baz);
          $stop();
       end
       if ($bits(qux3) != foo_inst3.baz) begin
          $display("%m: bits of qux3 != bits of foo_inst3.baz (%0d, %0d)",
                   $bits(qux3), foo_inst3.baz);
          $stop();
       end
       if (bar_bits != foo_wrapper_inst.foo_inst.baz) begin
          $display("%m: bar_bits != bits of foo_wrapper_inst.foo_inst.baz (%0d, %0d)",
                   bar_bits, foo_wrapper_inst.foo_inst.baz);
          $stop();
       end
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
      if (bar_size_wrapper != bar_bits) begin
         $display("%m: bar_size_wrapper != bar_bits (%0d, %0d)",
                 bar_size_wrapper, bar_bits);
         $stop();
      end
   end

   genvar m;
   generate
      for (m = 1; m <= 8; m+=1) begin : gen_m
            initial begin
                if (m != foo_inst.baz) begin
                   $display("%m: m != bits of foo_inst.baz (%0d, %0d)",
                            m, foo_inst.baz);
                   $stop();
                end
            end

            foo #(.bar (logic[m-1:0])) foo_inst (.bar_size ());
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
