// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   reg [31:0] state;  initial state=0;

   wire A = state[0];
   wire OE = state[1];
   wire Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9;
   wire [3:0] Z10;
   wire       Z11;

   Test1 test1(/*AUTOINST*/
               // Inouts
               .Z1                      (Z1),
               // Inputs
               .OE                      (OE),
               .A                       (A));

   Test2 test2(/*AUTOINST*/
               // Inouts
               .Z2                      (Z2),
               // Inputs
               .OE                      (OE),
               .A                       (A));

   Test3 test3(/*AUTOINST*/
               // Inouts
               .Z3                      (Z3),
               // Inputs
               .OE                      (OE),
               .A                       (A));

   Test4 test4(/*AUTOINST*/
               // Outputs
               .Z4                      (Z4),
               // Inouts
               .Z5                      (Z5));

   Test5 test5(/*AUTOINST*/
               // Inouts
               .Z6                      (Z6),
               .Z7                      (Z7),
               .Z8                      (Z8),
               .Z9                      (Z9),
               // Inputs
               .OE                      (OE));

   Test6 test6(/*AUTOINST*/
               // Inouts
               .Z10                     (Z10[3:0]),
               // Inputs
               .OE                      (OE));

   Test7 test7(/*AUTOINST*/
               // Outputs
               .Z11                     (Z11),
               // Inputs
               .state                   (state[2:0]));

   always @(posedge clk) begin
      state <= state + 1;
`ifdef TEST_VERBOSE
      $write("[%0t] state=%d Z1=%b 2=%b 3=%b 4=%b 5=%b 6=%b 7=%b 8=%b 9=%b 10=%b 11=%b\n",
             $time, state, Z1,Z2,Z3,Z4,Z5,Z6,Z7,Z8,Z9,Z10,Z11);
`endif

      if(state == 0) begin
         if(Z1 !== 1'b1) $stop;  // tests pullups
         if(Z2 !== 1'b1) $stop;
         if(Z3 !== 1'b1) $stop;
`ifndef VERILATOR
         if(Z4 !== 1'b1) $stop;
`endif
         if(Z5 !== 1'b1) $stop;
         if(Z6 !== 1'b1) $stop;
         if(Z7 !== 1'b0) $stop;
         if(Z8 !== 1'b0) $stop;
         if(Z9 !== 1'b1) $stop;
         if(Z10 !== 4'b0001) $stop;
         if(Z11 !== 1'b0) $stop;
      end
      else if(state == 1) begin
         if(Z1 !== 1'b1) $stop;  // tests pullup
         if(Z2 !== 1'b1) $stop;
         if(Z3 !== 1'b1) $stop;
`ifndef VERILATOR
         if(Z4 !== 1'b1) $stop;
`endif
         if(Z5 !== 1'b1) $stop;
         if(Z6 !== 1'b1) $stop;
         if(Z7 !== 1'b0) $stop;
         if(Z8 !== 1'b0) $stop;
         if(Z9 !== 1'b1) $stop;
         if(Z10 !== 4'b0001) $stop;
         if(Z11 !== 1'b1) $stop;
      end
      else if(state == 2) begin
         if(Z1 !== 1'b0) $stop; // tests output driver low
         if(Z2 !== 1'b0) $stop;
         if(Z3 !== 1'b1 && Z3 !== 1'bx) $stop;  // Conflicts
`ifndef VERILATOR
         if(Z4 !== 1'b1) $stop;
`endif
         if(Z5 !== 1'b1) $stop;
         if(Z6 !== 1'b0) $stop;
         if(Z7 !== 1'b1) $stop;
         if(Z8 !== 1'b1) $stop;
         if(Z9 !== 1'b0) $stop;
         if(Z10 !== 4'b0010) $stop;
         //if(Z11 !== 1'bx) $stop;  // Doesn't matter
      end
      else if(state == 3) begin
         if(Z1 !== 1'b1) $stop; // tests output driver high
         if(Z2 !== 1'b1) $stop;
         if(Z3 !== 1'b1) $stop;
`ifndef VERILATOR
         if(Z4 !== 1'b1) $stop;
`endif
         if(Z5 !== 1'b1) $stop;
         if(Z6 !== 1'b0) $stop;
         if(Z7 !== 1'b1) $stop;
         if(Z8 !== 1'b1) $stop;
         if(Z9 !== 1'b0) $stop;
         if(Z10 !== 4'b0010) $stop;
         if(Z11 !== 1'b1) $stop;
      end
      else if(state == 4) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
   pullup(Z1);
   pullup(Z2);
   pullup(Z3);
   pullup(Z4);
   pullup(Z5);
   pullup(Z6);
   pulldown(Z7);
   pullup(Z8);
   pulldown(Z9);
   pulldown pd10[3:0] (Z10);
endmodule


module Test1(input OE, input A, inout Z1);
   assign Z1 = (OE) ? A : 1'bz;
endmodule

module Test2(input OE, input A, inout Z2);
   assign Z2 = (OE) ? A : 1'bz;
endmodule


// mixed low-Z and tristate
module Test3(input OE, input A, inout Z3);
   assign Z3 = (OE) ? A : 1'bz;
   assign Z3 = 1'b1;
endmodule


// floating output and inout
`ifndef VERILATOR
// Note verilator doesn't know to make Z4 a tristate unless marked an inout
`endif
module Test4(output Z4, inout Z5);
endmodule


// AND gate tristates
module Test5(input OE, inout Z6, inout Z7, inout Z8, inout Z9);
   assign Z6 = (OE) ? 1'b0 : 1'bz;
   assign Z7 = (OE) ? 1'b1 : 1'bz;
   assign Z8 = (OE) ? 1'bz : 1'b0;
   assign Z9 = (OE) ? 1'bz : 1'b1;
endmodule

// AND gate tristates
module Test6(input OE, inout [3:0] Z10);
   wire [1:0] i;
   Test6a a (.OE(OE), .Z({Z10[0],Z10[1]}));
   Test6a b (.OE(~OE), .Z({Z10[2],Z10[0]}));
endmodule

module Test6a(input OE, inout [1:0] Z);
   assign Z = (OE) ? 2'b01 : 2'bzz;
endmodule

module Test7(input [2:0] state, output reg Z11);
   always @(*) begin
      casez (state)
        3'b000:  Z11 = 1'b0;
        3'b0?1:  Z11 = 1'b1;
        default: Z11 = 1'bx;
      endcase
   end
endmodule

// This is not implemented yet
//module Test3(input OE, input A, inout Z3);
//   always @(*) begin
//      if(OE) begin
//       Z3 = A;
//      end else begin
//       Z3 = 1'bz;
//      end
//   end
//endmodule
