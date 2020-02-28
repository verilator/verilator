// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Todd Strader.

module foo
   #(parameter type a_type = logic,
     parameter type b_type = int)
   ();

   initial begin
      if (type(a_type) != type(logic[7:0])) begin
         $display("%%Error: a_type is wrong");
         $stop();
      end

      if (type(b_type) != type(real)) begin
         $display("%%Error: b_type is wrong");
         $stop();
      end

      if (type(a_type) == type(logic)) begin
         $display("%%Error: a_type is the default value");
         $stop();
      end

      if (type(b_type) == type(int)) begin
         $display("%%Error: b_type is the default value");
         $stop();
      end

      if (type(a_type) == type(b_type)) begin
         $display("%%Error: a_type equals b_type");
         $stop();
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module t();

   foo #(
      .a_type (logic[7:0]),
      .b_type (real)) the_foo ();

endmodule
