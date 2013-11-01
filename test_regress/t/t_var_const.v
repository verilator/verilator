// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   const logic [2:0] five = 3'd5;

   const logic unsigned [31:0] var_const = 22;
   logic [7:0] res_const;
   assign res_const = var_const[7:0];  // bug693

   always @ (posedge clk) begin
      if (five !== 3'd5) $stop;
      if (res_const !== 8'd22) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
