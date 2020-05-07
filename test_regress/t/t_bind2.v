// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Ed Lander.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off WIDTH

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   reg    [7:0]  p1;
   reg [7:0] 	 p2;
   reg [7:0] 	 p3;

   initial begin
      p1 = 8'h01;
      p2 = 8'h02;
      p3 = 8'h03;
   end

   parameter int param1 = 8'h11;
   parameter int param2 = 8'h12;
   parameter int param3 = 8'h13;

   targetmod i_targetmod (/*AUTOINST*/
			  // Inputs
			  .clk			(clk));

   //Binding i_targetmod to mycheck --instantiates i_mycheck inside i_targetmod
   //param1 not over-riden (as mycheck)			(=> 0x31)
   //param2 explicitly bound to targetmod value	(=> 0x22)
   //param3 explicitly bound to top value			(=> 0x13)
   //p1 implictly bound (.*), takes value from targetmod	(=> 0x04)
   //p2 explictly bound to targetmod						(=> 0x05)
   //p3 explictly bound to top								(=> 0x03)

   // Alternative unsupported form is i_targetmod
   bind targetmod mycheck
     #(
       .param2(param2),
       .param3(param3)
       )
   i_mycheck (.p2(p2), .p3(p3), .*);

endmodule

module targetmod (input clk);
   reg	[7:0] p1;
   reg [7:0]  p2;
   reg [7:0]  p3;

   parameter int param1 = 8'h21;
   parameter int param2 = 8'h22;
   parameter int param3 = 8'h23;

   initial begin
      p1 = 8'h04;
      p2 = 8'h05;
      p3 = 8'h06;
   end
endmodule

module mycheck (/*AUTOARG*/
   // Inputs
   clk, p1, p2, p3
   );

   input clk;
   input [7:0] p1;
   input [7:0] p2;
   input [7:0] p3;

   parameter int param1 = 8'h31;
   parameter int param2 = 8'h32;
   parameter int param3 = 8'h33;

   always @ (posedge clk) begin
      `checkh(param1,8'h31);
      `checkh(param2,8'h22);
      `checkh(param3,8'h23);
      `checkh(p1,8'h04);
      `checkh(p2,8'h05);
      `checkh(p3,8'h06);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
