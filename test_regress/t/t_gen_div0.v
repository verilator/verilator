// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOINST*/);

   Test #(
          .BIT_WIDTH   (72),
          .BYTE_WIDTH  (9)
          )

   u_test_inst();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module Test ();

   parameter BIT_WIDTH   = "";
   parameter BYTE_WIDTH  = "";

   localparam BYTES = BIT_WIDTH / BYTE_WIDTH;

   wire [BYTES - 1:0] i;
   wire [BYTES - 1:0] o;

   genvar g;
   generate
      for (g = 0; g < BYTES; g = g + 1) begin: gen
           assign o[g] = (i[g] !== 1'b0);
        end
   endgenerate
endmodule

