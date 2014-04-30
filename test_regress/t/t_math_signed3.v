// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/);

   // verilator lint_off WIDTH
   wire [1:0]        bug729_au = ~0;
   wire signed [1:0] bug729_as = ~0;
   wire [2:0] 	     bug729_b = ~0;
   // the $signed output is unsigned because the input is unsigned; the signedness does not change.
   wire [0:0] 	     bug729_yuu = $signed(2'b11)  == 3'b111;   //1'b0
   wire [0:0] 	     bug729_ysu = $signed(2'sb11) == 3'b111;   //1'b0
   wire [0:0] 	     bug729_yus = $signed(2'b11)  == 3'sb111;  //1'b1
   wire [0:0] 	     bug729_yss = $signed(2'sb11) == 3'sb111;  //1'b1
   wire [0:0] 	     bug729_zuu = 2'sb11 == 3'b111;   //1'b0
   wire [0:0] 	     bug729_zsu = 2'sb11 == 3'b111;   //1'b0
   wire [0:0] 	     bug729_zus = 2'sb11 == 3'sb111;  //1'b1
   wire [0:0] 	     bug729_zss = 2'sb11 == 3'sb111;  //1'b1

   wire [3:0] 	     bug733_a = 4'b0010;
   wire [3:0] 	     bug733_yu = $signed(|bug733_a); // 4'b1111 note | is always unsigned
   wire signed [3:0] bug733_ys = $signed(|bug733_a); // 4'b1111

   wire [3:0] 	     bug733_zu = $signed(2'b11);  // 4'b1111
   wire signed [3:0] bug733_zs = $signed(2'sb11); // 4'b1111

   // When RHS of assignment is fewer bits than lhs, RHS sign or zero extends based on RHS's sign

   wire [3:0] 	     bug733_qu = 2'sb11;  // 4'b1111
   wire signed [3:0] bug733_qs = 2'sb11; // 4'b1111
   reg signed [32:0] bug349_s;
   reg signed [32:0] bug349_u;

   wire signed [1:0] sb11 = 2'sb11;

   wire [3:0] 	     subout_u;
   sub sub (.a(2'sb11), .z(subout_u));
   initial `checkh(subout_u, 4'b1111);

   wire [5:0] 	     cond_a = 1'b1 ? 3'sb111 : 5'sb11111;
   initial `checkh(cond_a, 6'b111111);
   wire [5:0] 	     cond_b = 1'b0 ? 3'sb111 : 5'sb11111;
   initial `checkh(cond_b, 6'b111111);

   initial begin
      // verilator lint_on WIDTH
      `checkh(bug729_yuu, 1'b0);
      `checkh(bug729_ysu, 1'b0);
      `checkh(bug729_yus, 1'b1);
      `checkh(bug729_yss, 1'b1);

      `checkh(bug729_zuu, 1'b0);
      `checkh(bug729_zsu, 1'b0);
      `checkh(bug729_zus, 1'b1);
      `checkh(bug729_zss, 1'b1);

      `checkh(bug733_yu, 4'b1111);
      `checkh(bug733_ys, 4'b1111);

      `checkh(bug733_zu, 4'b1111);
      `checkh(bug733_zs, 4'b1111);

      `checkh(bug733_qu, 4'b1111);
      `checkh(bug733_qs, 4'b1111);

      // verilator lint_off WIDTH
      bug349_s = 4'sb1111;
      `checkh(bug349_s, 33'h1ffffffff);
      bug349_u = 4'sb1111;
      `checkh(bug349_u, 33'h1ffffffff);

      bug349_s = 4'sb1111 - 1'b1;
      `checkh(bug349_s,33'he);

      bug349_s = 4'sb1111 - 5'b00001;
      `checkh(bug349_s,33'he);

      case (2'sb11)
	4'b1111: ;
	default: $stop;
      endcase

      case (sb11)
	4'b1111: ;
	default: $stop;
      endcase

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub (input [3:0] a,
	    output [3:0] z);
   assign z = a;
endmodule
